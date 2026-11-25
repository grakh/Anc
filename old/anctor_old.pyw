#! python3
# -*- coding: utf-8 -*-
import sys, os, traceback

def _fatal(msg):
    """Показать ошибку запуска в окне и записать в лог рядом со скриптом."""
    info = (msg + '\n\nPython: ' + sys.executable + '\nВерсия: ' + sys.version)
    try:
        log = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'anctor_error.log')
        with open(log, 'a', encoding='utf-8') as f:
            f.write(info + '\n' + '=' * 60 + '\n')
    except Exception:
        pass
    try:
        import tkinter, tkinter.messagebox
        r = tkinter.Tk(); r.withdraw()
        tkinter.messagebox.showerror('Anctor: ошибка запуска', info)
        r.destroy()
    except Exception:
        if sys.stdout is not None:          # под pythonw консоли нет
            print(info)
            try:
                input('Нажмите Enter...')
            except Exception:
                pass
    sys.exit(1)

try:
    from PIL import ImageTk
    from PIL import Image as Im
except ImportError:
    _fatal('Не установлен Pillow для этого Python.\n'
           'Установите командой:\n"' + sys.executable + '" -m pip install pillow')

def _excepthook(t, v, tb):
    _fatal(''.join(traceback.format_exception(t, v, tb)))
sys.excepthook = _excepthook

from tkinter import *
from tkinter.ttk import Progressbar
from tkinter.messagebox import *
from tkinter.filedialog import *
from xml.etree.ElementTree import parse
import os, sys
import re
import math
from collections import defaultdict
import json
import hashlib

allanc = []
mark = False
ver = 'Anctor V5.9'

# ============================================================
# === ГЕОМЕТРИЧЕСКИЕ ФУНКЦИИ ===
# ============================================================

def get_arc_center_from_r(x0, y0, x1, y1, r_val, is_cw):
    dx = x1 - x0
    dy = y1 - y0
    d = math.hypot(dx, dy)
    if d < 1e-6:
        return x0, y0
    r = abs(r_val)
    if r < d / 2.0:
        r = d / 2.0
    mx = (x0 + x1) / 2.0
    my = (y0 + y1) / 2.0
    h = math.sqrt(max(0.0, r * r - (d / 2.0) ** 2))
    px = -dy / d
    py = dx / d
    if r_val < 0:
        is_cw = not is_cw
    if is_cw:
        cx = mx - h * px
        cy = my - h * py
    else:
        cx = mx + h * px
        cy = my + h * py
    return cx, cy

def generate_arc_points(x0, y0, x1, y1, cx, cy, is_cw):
    r = math.hypot(x0 - cx, y0 - cy)
    if r < 1e-6:
        return [(x1, y1)]
    start_angle = math.atan2(y0 - cy, x0 - cx)
    end_angle = math.atan2(y1 - cy, x1 - cx)
    if is_cw:
        while end_angle >= start_angle:
            end_angle -= 2 * math.pi
    else:
        while end_angle <= start_angle:
            end_angle += 2 * math.pi
    sweep = end_angle - start_angle
    steps = max(4, int(abs(sweep) / (math.pi / 4)))
    arc_pts = []
    for k in range(1, steps + 1):
        t = k / steps
        ang = start_angle + t * sweep
        px = cx + r * math.cos(ang)
        py = cy + r * math.sin(ang)
        arc_pts.append((px, py))
    return arc_pts

def _point_seg_dist(px, py, x1, y1, x2, y2):
    dx, dy = x2 - x1, y2 - y1
    len_sq = dx * dx + dy * dy
    if len_sq < 1e-12:
        return math.hypot(px - x1, py - y1), (x1, y1)
    t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / len_sq))
    nx, ny = x1 + t * dx, y1 + t * dy
    return math.hypot(px - nx, py - ny), (nx, ny)

def _seg_seg_dist(x1, y1, x2, y2, x3, y3, x4, y4):
    d1, p1 = _point_seg_dist(x3, y3, x1, y1, x2, y2)
    d2, p2 = _point_seg_dist(x4, y4, x1, y1, x2, y2)
    d3, p3 = _point_seg_dist(x1, y1, x3, y3, x4, y4)
    d4, p4 = _point_seg_dist(x2, y2, x3, y3, x4, y4)
    min_d = min(d1, d2, d3, d4)
    if min_d == d1: return min_d, p1
    if min_d == d2: return min_d, p2
    if min_d == d3: return min_d, p3
    return min_d, p4

# ============================================================
# === ПРОВЕРКА ЛИДОВ (врезание подвода/отвода в контур) ===
# ============================================================
# Центр инструмента на лиде (со смещением G41/G42, как у станка) не должен
# подходить к запрограммированному контуру ближе радиуса инструмента.
#
# Структура блока (постпроцессор AEC GVM / MTX):
#   G0  X Y         ;40,9   точка врезания
#   G42 X Y         ;       прямая подвода (включение коррекции)
#   G12 X Y         ;50,10  дуга подвода, касательная к СЛЕДУЮЩЕМУ элементу
#   G2/G3/G1 ...            контур
#   G13 X Y         ;50,15  дуга отвода, касательная к ПРЕДЫДУЩЕМУ элементу
#   G1 G40 X Y      ;40,18  прямая отвода (выключение коррекции)

_RE_LG = re.compile(r'\bG(\d+)', re.IGNORECASE)
_RE_LX = re.compile(r'\bX\s*([+-]?\d*\.?\d+)', re.IGNORECASE)
_RE_LY = re.compile(r'\bY\s*([+-]?\d*\.?\d+)', re.IGNORECASE)
_RE_LR = re.compile(r'\bR\s*([+-]?\d*\.?\d+)', re.IGNORECASE)

def _tangent_arc(x0, y0, tx, ty, x1, y1):
    """Дуга из (x0,y0) с касательной (tx,ty) в точку (x1,y1) -> (центр, cw) или None."""
    nx, ny = -ty, tx
    vx, vy = x1 - x0, y1 - y0
    den = 2.0 * (vx * nx + vy * ny)
    if abs(den) < 1e-9:
        return None
    k = (vx * vx + vy * vy) / den
    return (x0 + k * nx, y0 + k * ny), (k < 0)

def _el_tangent(el, at_end):
    (x0, y0), (x1, y1) = el['p0'], el['p1']
    if el['type'] == 'arc':
        cx, cy = el['c']
        px, py = (x1, y1) if at_end else (x0, y0)
        rx, ry = px - cx, py - cy
        r = math.hypot(rx, ry)
        return (ry / r, -rx / r) if el['cw'] else (-ry / r, rx / r)
    d = math.hypot(x1 - x0, y1 - y0)
    return ((x1 - x0) / d, (y1 - y0) / d)

def sample_element(el, step=0.02):
    """Точки элемента + правая нормаль к направлению движения."""
    (x0, y0), (x1, y1) = el['p0'], el['p1']
    if el['type'] == 'arc':
        cx, cy = el['c']
        r = math.hypot(x0 - cx, y0 - cy)
        a0 = math.atan2(y0 - cy, x0 - cx)
        a1 = math.atan2(y1 - cy, x1 - cx)
        if el['cw']:
            while a1 >= a0:
                a1 -= 2 * math.pi
        else:
            while a1 <= a0:
                a1 += 2 * math.pi
        n = max(2, int(abs(a1 - a0) * r / step))
        out = []
        for k in range(n + 1):
            a = a0 + (a1 - a0) * k / n
            ux, uy = math.cos(a), math.sin(a)
            nrm = (-ux, -uy) if el['cw'] else (ux, uy)
            out.append(((cx + r * ux, cy + r * uy), nrm))
        return out
    L = math.hypot(x1 - x0, y1 - y0)
    tx, ty = (x1 - x0) / L, (y1 - y0) / L
    nrm = (ty, -tx)
    n = max(1, int(L / step))
    return [((x0 + (x1 - x0) * k / n, y0 + (y1 - y0) * k / n), nrm) for k in range(n + 1)]

def parse_anc_parts(path):
    """Разбор файла на PART'ы с элементами lead_in / contour / lead_out.
    Возвращает (parts, equidistant)."""
    parts, cur = [], None
    x = y = 0.0
    mode, comp = 0, 40
    last_tan = None
    equidistant = None
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            if 'SSDE[SD.USR.ToolData.ProgToolEquidistant' in line:
                s = line[line.rfind('=') + 1: line.rfind(']')].strip()
                try:
                    if '/' in s:
                        a, b = s.split('/')
                        equidistant = float(a) / float(b)
                    else:
                        equidistant = float(s)
                except ValueError:
                    pass
            code = line.split(';')[0]
            # ── РОЛЬ СТРОКИ ПО ТЕГУ ПОСТА (не по G-коду) ──
            # С 2026-10 пост Anderson пишет заходы и выходы настоящими
            # дугами: `G2 X.. Y.. R.. ;50,10 G12` вместо канонического
            # цикла `G12 X.. Y.. ;50,10`. По G-коду такая строка
            # неотличима от контурной дуги, и лид уезжал в 'contour':
            # дуга переставала проверяться, а ramp-модель прямой части
            # упиралась в собственную же дугу лида и давала ровно
            # 0.037 мм «врезания» на КАЖДОМ лиде.
            #
            # Теги `;50,10`/`;60,10` (заход) и `;50,15`/`;60,15` (выход)
            # не менялись ни в одной версии поста, поэтому роль берём по
            # ним, а G-код оставляем только как запасной путь для старых
            # файлов.
            _tag_kind = None
            if ';50,10' in line or ';60,10' in line:
                _tag_kind = 'lead_in'
            elif ';50,15' in line or ';60,15' in line:
                _tag_kind = 'lead_out'
            if 'PREPART' in code:
                cur = {'els': [], 'eq': equidistant}
                parts.append(cur)
                comp, last_tan = 40, None
            gs = [int(v) for v in _RE_LG.findall(code)]
            for v in gs:
                if v in (0, 1, 2, 3, 12, 13):
                    mode = v
                elif v in (40, 41, 42):
                    comp = v
            mx, my = _RE_LX.search(code), _RE_LY.search(code)
            if not (mx or my):
                continue
            nx = float(mx.group(1)) if mx else x
            ny = float(my.group(1)) if my else y
            if abs(nx - x) < 1e-9 and abs(ny - y) < 1e-9:
                continue
            if mode == 0 or cur is None:
                x, y = nx, ny
                continue
            if _tag_kind is not None:
                kind = _tag_kind
            elif 41 in gs or 42 in gs or mode == 12:
                kind = 'lead_in'
            elif 40 in gs or mode == 13:
                kind = 'lead_out'
            else:
                kind = 'contour'
            el = {'kind': kind, 'p0': (x, y), 'p1': (nx, ny), 'comp': comp,
                  'comp_on': (41 in gs or 42 in gs), 'comp_off': (40 in gs),
                  'type': 'line'}
            mr = _RE_LR.search(code)
            if mode in (2, 3) and mr:
                cw = (mode == 2)
                el.update(type='arc', c=get_arc_center_from_r(x, y, nx, ny, float(mr.group(1)), cw), cw=cw)
            elif mode == 12:
                el['type'] = 'tan_in'
            elif mode == 13 and last_tan:
                res = _tangent_arc(x, y, last_tan[0], last_tan[1], nx, ny)
                if res:
                    el.update(type='arc', c=res[0], cw=res[1])
            last_tan = None if el['type'] == 'tan_in' else _el_tangent(el, True)
            cur['els'].append(el)
            x, y = nx, ny
    # G12: дуга, приходящая касательно к следующему элементу
    for p in parts:
        els = p['els']
        for k, el in enumerate(els):
            if el['type'] != 'tan_in':
                continue
            el['type'] = 'line'
            if k + 1 < len(els):
                t = _el_tangent(els[k + 1], False)
                res = _tangent_arc(el['p1'][0], el['p1'][1], -t[0], -t[1], el['p0'][0], el['p0'][1])
                if res:
                    el.update(type='arc', c=res[0], cw=not res[1])
    return parts, equidistant

def lead_tool_center(part, r):
    """Точки центра инструмента на лидах: (x, y, kind)."""
    els = part['els']
    out = []
    for k, el in enumerate(els):
        if el['kind'] == 'contour':
            continue
        pts = sample_element(el)
        m = len(pts) - 1
        if el['comp_on'] and k + 1 < len(els):
            side = 1 if el['comp'] == 42 else -1
            n = sample_element(els[k + 1])[0][1]
            for i, (p, _) in enumerate(pts):
                f = i / m
                out.append((p[0] + side * r * n[0] * f, p[1] + side * r * n[1] * f, el['kind']))
        elif el['comp_off'] and k > 0:
            prev = els[k - 1]
            side = 1 if prev['comp'] == 42 else -1
            n = sample_element(prev)[-1][1]
            for i, (p, _) in enumerate(pts):
                f = 1 - i / m
                out.append((p[0] + side * r * n[0] * f, p[1] + side * r * n[1] * f, el['kind']))
        else:
            side = 1 if el['comp'] == 42 else (-1 if el['comp'] == 41 else 0)
            for p, n in pts:
                out.append((p[0] + side * r * n[0], p[1] + side * r * n[1], el['kind']))
    return out

def _part_r(p, r):
    return p.get('eq') or r

def find_lead_gouges(parts, r, tol=0.01, progress=None):
    """Список врезаний: (part_idx, target_part_idx, kind, depth, (x, y)).
    depth — на сколько мм инструмент заходит за кромку."""
    cell = max([r] + [_part_r(p, r) for p in parts] + [0.1])
    grid = defaultdict(list)
    segs = []
    for pi, p in enumerate(parts):
        for el in p['els']:
            if el['kind'] != 'contour':
                continue
            pts = [q for q, _ in sample_element(el, 0.05)]
            for a, b in zip(pts, pts[1:]):
                si = len(segs)
                segs.append((pi, a, b))
                for gx in range(int(min(a[0], b[0]) // cell), int(max(a[0], b[0]) // cell) + 1):
                    for gy in range(int(min(a[1], b[1]) // cell), int(max(a[1], b[1]) // cell) + 1):
                        grid[(gx, gy)].append(si)
    worst = {}
    for pi, p in enumerate(parts):
        if progress:
            progress(pi, len(parts))
        rp = _part_r(p, r)
        for x, y, kind in lead_tool_center(p, rp):
            gx, gy = int(x // cell), int(y // cell)
            seen = set()
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    for si in grid.get((gx + dx, gy + dy), ()):
                        if si in seen:
                            continue
                        seen.add(si)
                        pj, a, b = segs[si]
                        d, _ = _point_seg_dist(x, y, a[0], a[1], b[0], b[1])
                        if d < rp - tol:
                            key = (pi, pj, kind)
                            depth = rp - d
                            if key not in worst or depth > worst[key][0]:
                                worst[key] = (depth, (x, y))
    rows = [(pi, pj, kind, depth, pt)
            for (pi, pj, kind), (depth, pt) in worst.items()]

    # ── СКЛЕЙКА ДУБЛЕЙ ──
    # Один нож даёт в программе ДВА PART'а (внутренний и внешний проход)
    # с ОДНИМ И ТЕМ ЖЕ контуром. Поэтому каждое врезание находилось
    # дважды — против обоих — и список удваивался: на 198 реальных
    # находок печаталось 396. Склеиваем записи одного лида, попавшие в
    # одну и ту же точку, оставляя самую глубокую.
    rows.sort(key=lambda r: -r[3])
    merged = []
    for row in rows:
        pi, pj, kind, depth, pt = row
        dup = False
        for m in merged:
            if m[0] == pi and m[2] == kind and \
                    math.hypot(m[4][0] - pt[0], m[4][1] - pt[1]) < 0.05:
                dup = True
                break
        if not dup:
            merged.append(row)
    return merged

def find_contour_collisions(parts, r, tol=0.01, progress=None):
    """Контур одного PART срезает кромку ДРУГОГО PART.
    Центр инструмента на контуре (со смещением G41/G42) ближе r к чужому контуру.
    Возвращает (part_idx, target_part_idx, depth, (x, y)) — худшая точка на пару."""
    cell = max([r] + [_part_r(p, r) for p in parts] + [0.1])
    grid = defaultdict(list)
    segs = []
    for pi, p in enumerate(parts):
        for el in p['els']:
            if el['kind'] != 'contour':
                continue
            pts = [q for q, _ in sample_element(el, 0.05)]
            for a, b in zip(pts, pts[1:]):
                si = len(segs)
                segs.append((pi, a, b))
                for gx in range(int(min(a[0], b[0]) // cell), int(max(a[0], b[0]) // cell) + 1):
                    for gy in range(int(min(a[1], b[1]) // cell), int(max(a[1], b[1]) // cell) + 1):
                        grid[(gx, gy)].append(si)
    worst = {}
    for pi, p in enumerate(parts):
        if progress:
            progress(pi, len(parts))
        rp = _part_r(p, r)
        for el in p['els']:
            if el['kind'] != 'contour':
                continue
            side = 1 if el['comp'] == 42 else (-1 if el['comp'] == 41 else 0)
            if side == 0:
                continue
            for q, n in sample_element(el, 0.05):
                x, y = q[0] + side * rp * n[0], q[1] + side * rp * n[1]
                gx, gy = int(x // cell), int(y // cell)
                seen = set()
                own_min = float('inf')
                hits = {}
                for dx in (-1, 0, 1):
                    for dy in (-1, 0, 1):
                        for si in grid.get((gx + dx, gy + dy), ()):
                            if si in seen:
                                continue
                            seen.add(si)
                            pj, a, b = segs[si]
                            d, _ = _point_seg_dist(x, y, a[0], a[1], b[0], b[1])
                            if pj == pi:
                                own_min = min(own_min, d)
                            elif d < rp - tol and d < hits.get(pj, float('inf')):
                                hits[pj] = d
                # точка, которая режет свой же контур, — перехлёст эквидистанты
                # на внутреннем углу; станок её срезает, не учитываем
                if own_min < rp - tol:
                    continue
                for pj, d in hits.items():
                    depth = rp - d
                    if (pi, pj) not in worst or depth > worst[(pi, pj)][0]:
                        worst[(pi, pj)] = (depth, (x, y))
    return [(pi, pj, depth, pt) for (pi, pj), (depth, pt) in worst.items()]

# ============================================================
# === ФУНКЦИИ ПРОВЕРКИ ПЕРЕСЕЧЕНИЙ ===
# ============================================================

def find_path_intersections(cached_paths, file_vars, equidistant):
    """Пересечения между разными путями (cut-cut, cut-g0, g0-g0)."""
    radius = equidistant
    min_dist = radius * 2
    cell_size = min_dist if min_dist > 0 else 1.0

    all_segments = []
    path_bboxes = {}

    for file_path, path_data in cached_paths.items():
        var = file_vars.get(file_path)
        if var is not None and not var.get():
            continue
        for path_idx, points in enumerate(path_data.get('cut', [])):
            if len(points) < 2:
                continue
            xs = [p[0] for p in points]
            ys = [p[1] for p in points]
            bbox = (min(xs), min(ys), max(xs), max(ys))
            path_bboxes[(file_path, path_idx, False)] = bbox
            for i in range(len(points) - 1):
                all_segments.append((file_path, path_idx, False, points[i], points[i + 1]))
        for g0_idx, (x1, y1, x2, y2) in enumerate(path_data.get('g0', [])):
            bbox = (min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2))
            path_bboxes[(file_path, g0_idx, True)] = bbox
            all_segments.append((file_path, g0_idx, True, (x1, y1), (x2, y2)))

    grid = defaultdict(list)
    for idx, (f1, p1, is_g0_1, s1, e1) in enumerate(all_segments):
        min_x, max_x = min(s1[0], e1[0]), max(s1[0], e1[0])
        min_y, max_y = min(s1[1], e1[1]), max(s1[1], e1[1])
        for cx in range(int(min_x / cell_size), int(max_x / cell_size) + 1):
            for cy in range(int(min_y / cell_size), int(max_y / cell_size) + 1):
                grid[(cx, cy)].append(idx)

    raw = []
    checked_pairs = set()

    for idx1, (f1, p1, is_g0_1, s1, e1) in enumerate(all_segments):
        bbox1 = path_bboxes.get((f1, p1, is_g0_1))
        if not bbox1:
            continue
        min_x, max_x = min(s1[0], e1[0]), max(s1[0], e1[0])
        min_y, max_y = min(s1[1], e1[1]), max(s1[1], e1[1])
        for cx in range(int(min_x / cell_size), int(max_x / cell_size) + 1):
            for cy in range(int(min_y / cell_size), int(max_y / cell_size) + 1):
                for dx in range(-1, 2):
                    for dy in range(-1, 2):
                        cell_key = (cx + dx, cy + dy)
                        if cell_key not in grid:
                            continue
                        for idx2 in grid[cell_key]:
                            if idx2 <= idx1:
                                continue
                            f2, p2, is_g0_2, s2, e2 = all_segments[idx2]
                            if f1 == f2 and p1 == p2 and is_g0_1 == is_g0_2:
                                continue
                            pair_key = ((f1, p1, is_g0_1), (f2, p2, is_g0_2))
                            if pair_key in checked_pairs or ((f2, p2, is_g0_2), (f1, p1, is_g0_1)) in checked_pairs:
                                continue
                            bbox2 = path_bboxes.get((f2, p2, is_g0_2))
                            if not bbox2:
                                continue
                            if not (bbox1[0] <= bbox2[2] + min_dist and
                                    bbox1[2] >= bbox2[0] - min_dist and
                                    bbox1[1] <= bbox2[3] + min_dist and
                                    bbox1[3] >= bbox2[1] - min_dist):
                                continue
                            dist, point = _seg_seg_dist(s1[0], s1[1], e1[0], e1[1], s2[0], s2[1], e2[0], e2[1])
                            if dist < min_dist:
                                checked_pairs.add(pair_key)
                                t1 = "G0" if is_g0_1 else "cut"
                                t2 = "G0" if is_g0_2 else "cut"
                                raw.append((point, f1, f2, dist, t1, t2))

    return _clusterize(raw)

def find_self_intersections(cached_paths, file_vars, equidistant):
    """Самопересечения внутри одного контура."""
    radius = equidistant
    min_dist = radius * 2
    cell_size = min_dist if min_dist > 0 else 1.0

    raw = []

    for file_path, path_data in cached_paths.items():
        var = file_vars.get(file_path)
        if var is not None and not var.get():
            continue
        for path_idx, points in enumerate(path_data.get('cut', [])):
            if len(points) < 3:
                continue
            segments = [(points[i], points[i + 1]) for i in range(len(points) - 1)]
            n = len(segments)

            seg_grid = defaultdict(list)
            for idx, (s, e) in enumerate(segments):
                min_x, max_x = min(s[0], e[0]), max(s[0], e[0])
                min_y, max_y = min(s[1], e[1]), max(s[1], e[1])
                for cx in range(int(min_x / cell_size), int(max_x / cell_size) + 1):
                    for cy in range(int(min_y / cell_size), int(max_y / cell_size) + 1):
                        seg_grid[(cx, cy)].append(idx)

            self_checked = set()
            for idx1 in range(n):
                s1, e1 = segments[idx1]
                min_x, max_x = min(s1[0], e1[0]), max(s1[0], e1[0])
                min_y, max_y = min(s1[1], e1[1]), max(s1[1], e1[1])
                for cx in range(int(min_x / cell_size), int(max_x / cell_size) + 1):
                    for cy in range(int(min_y / cell_size), int(max_y / cell_size) + 1):
                        for dx in range(-1, 2):
                            for dy in range(-1, 2):
                                cell_key = (cx + dx, cy + dy)
                                if cell_key not in seg_grid:
                                    continue
                                for idx2 in seg_grid[cell_key]:
                                    if idx2 <= idx1:
                                        continue
                                    if abs(idx2 - idx1) <= 1:
                                        continue
                                    pair_key = (idx1, idx2)
                                    if pair_key in self_checked:
                                        continue
                                    s2, e2 = segments[idx2]
                                    dist, point = _seg_seg_dist(s1[0], s1[1], e1[0], e1[1], s2[0], s2[1], e2[0], e2[1])
                                    if dist < min_dist:
                                        self_checked.add(pair_key)
                                        raw.append((point, file_path, file_path, dist, path_idx))

    return _clusterize(raw)

def _clusterize(raw_intersections, cluster_threshold=0.3):
    if not raw_intersections:
        return []
    clusters = []
    for item in raw_intersections:
        point = item[0]
        merged = False
        for cluster in clusters:
            if math.hypot(point[0] - cluster['center'][0], point[1] - cluster['center'][1]) < cluster_threshold:
                cluster['points'].append(item)
                if item[3] < cluster['min_dist']:
                    cluster['min_dist'] = item[3]
                    cluster['min_point'] = point
                merged = True
                break
        if not merged:
            clusters.append({
                'center': point,
                'points': [item],
                'min_dist': item[3],
                'min_point': point
            })
    return [tuple(c['min_point']) + (c['points'][0][1], c['points'][0][2], c['min_dist']) + tuple(c['points'][0][4:]) for c in clusters]

# ============================================================
# === НАСТРОЙКИ (сохраняются рядом со скриптом) ===
# ============================================================

SETTINGS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'anctor_settings.json')
DEFAULT_SETTINGS = {'poll_count': 10, 'poll_interval': 5, 'auto_collisions': 0,
                    'fix_backup': 1,
                    # Fix G-code: ОДНО значение R_min на всю папку (одинаковая геометрия у всех программ)
                    'fix_dtip': 0.15,    # макс. превышение площадки (Tool-R) над номиналом, мм
                    'fix_ang': 90,       # макс. угол заточки, ° (если в программе меньше - берётся этот)
                    'fix_safety': 0.03,  # страховка, мм
                    'fix_rmin': 0,       # R_min основных программ вручную, мм (0 = считать автоматически)
                    'fix_corner_mask': 'corner',   # программы доработки мелких углов (подстроки через запятую)
                    'fix_corner_rmin': 0.5}        # мин. радиус угла по чертежу для corner (не 3D), мм; 0 = по инструменту
FLOAT_SETTINGS = ('fix_dtip', 'fix_ang', 'fix_safety', 'fix_rmin', 'fix_corner_rmin')
STR_SETTINGS = ('fix_corner_mask',)

def load_settings():
    st = dict(DEFAULT_SETTINGS)
    try:
        with open(SETTINGS_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        for k in st:
            if k in data:
                try:
                    if k in STR_SETTINGS:
                        st[k] = str(data[k])
                    elif k in FLOAT_SETTINGS:
                        st[k] = max(0.0, float(data[k]))
                    else:
                        st[k] = max(0, int(data[k]))
                except (TypeError, ValueError):
                    pass
    except Exception:
        pass
    return st

def save_settings(st):
    try:
        with open(SETTINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(st, f, ensure_ascii=False, indent=2)
        return True
    except Exception:
        return False

def dir_snapshot(d):
    """Снимок папки NC: имя, размер и время изменения файлов .anc."""
    snap = set()
    try:
        with os.scandir(d) as it:
            for e in it:
                if e.is_file() and e.name.lower().endswith('.anc'):
                    st = e.stat()
                    snap.add((e.name, st.st_size, st.st_mtime_ns))
    except OSError:
        pass
    return frozenset(snap)

def is_auto_collision_file(path):
    """Для автопроверки столкновений: только *_R.anc без 'revers' в имени."""
    name = os.path.basename(path).lower()
    return name.endswith('_r.anc') and 'revers' not in name

# ============================================================
# === КОРРЕКЦИЯ G-КОДА (ошибки Cornering / Corner peaks) ===
# ============================================================
# 1) "Cornering: Tool too big!" - внутренняя дуга (G42+G2 / G41+G3) с R меньше
#    фактического радиуса инструмента. Радиус дуги увеличивается до R_min,
#    концы дуги не меняются.
# 2) "Corner peaks: A contact point could not be found..." - микро-кадры
#    (длина < NF_MIN_LEN). Кадр удаляется, конец предыдущего кадра переносится
#    в его точку (контур остаётся замкнутым).
# Две группы программ в папке:
#   основные (черновые и чистовые) - ОДИН R_min на всех = худший инструмент группы + страховка,
#       геометрия у них одинаковая; увеличенная внутренняя дуга смещается в сторону инструмента,
#       т.е. основной инструмент только недорезает угол, который он и так не может пройти;
#   corner (имя содержит маску) - доработка мелких углов: R_min = мин. радиус угла по чертежу (0.5),
#       всё меньше - артефакты CAM; углы от R0.5 не трогаются. Для 3D (только ToolType = 1) правило 0.5
#       не действует - там R_min по худшему corner-инструменту.
#   r файла = (площадка_ном + dtip) + глубина*tan(max(угол_прогр, угол_макс)/2)

NF_MIN_LEN = 0.010          # мм, кадры короче считаются микро-кадрами (стойка: Cornering error 10219 'Split' на 7 мкм)
NF_BACKUP_DIR = '_orig_fix' # подпапка для оригиналов
_NF_MOTION_G = {0, 1, 2, 3, 12, 13}
_NF_TOKEN_OK = re.compile(r'^(G\d+(\.\d+)?|[XYZRIJKFSMHDT]-?\d*\.?\d+|[A-Z][A-Z0-9]*\([^)]*\))$')
_NF_WORD = re.compile(r'([XYZRIJKF])(-?\d*\.?\d+)')


def _nf_div(expr):
    expr = expr.strip()
    if '/' in expr:
        a, b = expr.split('/', 1)
        return float(a) / float(b)
    return float(expr)


def _nf_split(line):
    """(номер кадра, код, комментарий с ';')"""
    pos = line.find(';')
    code, comment = (line, '') if pos < 0 else (line[:pos], line[pos:])
    m = re.match(r'^(\s*N\d+\s+|\s*\d+\s+)', code)
    nnum = m.group(1) if m else ''
    return nnum, code[len(nnum):], comment


def _nf_sagitta(r, chord):
    h = r * r - chord * chord / 4.0
    return r - math.sqrt(h) if h > 0 else r


def _nf_fmt(v):
    return ('%.5f' % v).rstrip('0').rstrip('.')


NF_MANIFEST = 'fix_manifest.json'


def _nf_hash(data):
    return hashlib.sha1(data).hexdigest()


def _nf_manifest(bdir, data=None):
    """Чтение (data=None) / запись журнала: имя файла -> хэш записанной исправленной версии."""
    path = os.path.join(bdir, NF_MANIFEST)
    if data is None:
        try:
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            return {}
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=1)


def nc_tool_data(text):
    """(эквидистанта/2, радиус площадки, угол, глубина) из PRESETTINGS; чего нет - None."""
    def get(pat):
        mm = re.search(pat, text)
        return _nf_div(mm.group(1)) if mm else None
    return (get(r'ProgToolEquidistant\s*=\s*([\d./]+)'),
            get(r'SD\.WZRec\.UD\.Ed\[1\]\.Geo\.Rad\s*=\s*([\d./]+)'),
            get(r'SD\.WZRec\.UD\.Ed\[1\]\.Geo\.Ang\s*=\s*([\d./]+)'),
            get(r'ProgZDepth\s*=\s*ABS\(([\d./]+)\)'))


def nc_is_corner(name, mask):
    """Программа доработки мелких углов? mask - подстроки через запятую (без учёта регистра)."""
    n = name.lower()
    return any(m.strip().lower() in n for m in (mask or '').split(',') if m.strip())


def nc_is_3d(text):
    """3D-программа (Werkzeugtyp 1 = 3D)."""
    return re.search(r'ToolAdjust\.ToolType\s*=\s*1\b', text) is not None


def nc_worst_radius(text, dtip, ang_max):
    """Наибольший возможный радиус коррекции для программы (худший инструмент), или None."""
    rc, tip_r, ang, depth = nc_tool_data(text)
    if rc is None:
        return None
    if tip_r is not None and ang is not None and depth is not None and 0 < ang < 180:
        a_use = max(ang, ang_max or 0)
        r = tip_r + dtip + depth * math.tan(math.radians(a_use / 2.0))
        return max(r, rc)
    return rc + dtip


def nc_fix_text(text, dtip=0.15, ang_max=90, safety=0.03, min_len=NF_MIN_LEN, min_radius=None, max_dev=0.0005):
    """Проверка/коррекция текста NC-программы.
    Возвращает (новый_текст или None если правок нет, список строк отчёта, (дуг, микро, откл_мм))."""
    log = []
    crlf = '\r\n' in text
    lines = text.replace('\r\n', '\n').split('\n')

    m = re.search(r'ProgToolEquidistant\s*=\s*([\d./]+)', text)
    if not m:
        log.append('  нет ProgToolEquidistant - файл пропущен')
        return None, log, (0, 0, 0.0)
    rc = _nf_div(m.group(1))

    def get(pat):
        mm = re.search(pat, text)
        return _nf_div(mm.group(1)) if mm else None
    tip_r = get(r'SD\.WZRec\.UD\.Ed\[1\]\.Geo\.Rad\s*=\s*([\d./]+)')
    ang = get(r'SD\.WZRec\.UD\.Ed\[1\]\.Geo\.Ang\s*=\s*([\d./]+)')
    depth = get(r'ProgZDepth\s*=\s*ABS\(([\d./]+)\)')
    rgeo = None
    if tip_r is not None and ang is not None and depth is not None and 0 < ang < 180:
        rgeo = tip_r + depth * math.tan(math.radians(ang / 2.0))
        if abs(rgeo - rc) > 0.01 and depth > 0:
            implied = 2 * math.degrees(math.atan((rc - tip_r) / depth))
            log.append('  ВНИМАНИЕ: эквидистанта Ø%.4f не совпадает с резцом %g° '
                       '(Ø%.4f на гл. %.3f), соответствует углу ~%.1f° - проверьте инструмент в CAM'
                       % (2 * rc, ang, 2 * rgeo, depth, implied))
    if min_radius is not None:
        rmin = min_radius
    elif rgeo is not None:
        a_use = max(ang, ang_max or 0)
        r_worst = tip_r + dtip + depth * math.tan(math.radians(a_use / 2.0))
        rmin = max(rc, r_worst) + safety
        log.append('  R_min %.4f: площадка до %.3f, угол %g°, гл. %.3f -> инструмент до Ø%.3f'
                   % (rmin, tip_r + dtip, a_use, depth, 2 * r_worst))
    else:
        rmin = rc + dtip + safety
        log.append('  R_min %.4f: нет данных резца, эквидистанта %.4f + %.3f + %.3f'
                   % (rmin, rc, dtip, safety))
    rmin = math.ceil(rmin * 1e5 - 1e-6) / 1e5   # округление вверх до 5 знаков (как в программе)

    # --- разбор кадров XY ---
    blocks = []
    mode, comp = None, 40
    x = y = None
    for i, line in enumerate(lines):
        nnum, code, comment = _nf_split(line)
        toks = code.split()
        if not toks or not all(_NF_TOKEN_OK.match(t) for t in toks):
            continue
        gl = [float(t[1:]) for t in toks if t[0] == 'G']
        for g in gl:
            if g == 91:
                log.append('  G91 в строке %d - файл пропущен (поддерживается только G90)' % (i + 1))
                return None, log, (0, 0, 0.0)
            if g == int(g) and int(g) in _NF_MOTION_G:
                mode = int(g)
            if g in (40, 41, 42):
                comp = int(g)
        words = dict(_NF_WORD.findall(' '.join(toks)))
        if 'X' not in words and 'Y' not in words:
            continue
        nx = float(words['X']) if 'X' in words else x
        ny = float(words['Y']) if 'Y' in words else y
        blocks.append({'i': i, 'code': code, 'g': gl, 'w': words, 'mode': mode,
                       'comp': comp, 'x0': x, 'y0': y, 'x1': nx, 'y1': ny})
        x, y = nx, ny

    def plain(b):
        return (b['mode'] in (1, 2, 3) and b['comp'] in (41, 42)
                and not re.search(r'[A-Z]{2,}\(', b['code'])
                and all(g in (1, 2, 3) for g in b['g']))

    def set_end(b, nx, ny):
        nnum, code, comment = _nf_split(lines[b['i']])
        if 'X' in b['w']:
            code = re.sub(r'X-?\d*\.?\d+', 'X' + _nf_fmt(nx), code, count=1)
        if 'Y' in b['w']:
            code = re.sub(r'Y-?\d*\.?\d+', 'Y' + _nf_fmt(ny), code, count=1)
        lines[b['i']] = nnum + code + comment
        b['x1'], b['y1'] = nx, ny

    delete = set()
    n_arc = n_micro = 0
    maxdev = 0.0

    # --- микро-кадры: поглощаются предыдущим кадром, если его форма почти не меняется ---
    def elem_dev(b, ex, ey, pts):
        """Макс. отклонение точек pts от кадра b, если его конец перенести в (ex, ey); None - нельзя."""
        x0, y0 = b['x0'], b['y0']
        if b['mode'] == 1:
            dx, dy = ex - x0, ey - y0
            L2 = dx * dx + dy * dy
            if L2 < 1e-14:
                return None
            dev = 0.0
            for px, py in pts:
                t = max(0.0, min(1.0, ((px - x0) * dx + (py - y0) * dy) / L2))
                dev = max(dev, math.hypot(px - (x0 + t * dx), py - (y0 + t * dy)))
            return dev
        if 'R' not in b['w']:
            return None
        R = float(b['w']['R'])
        if R <= 0:
            return None
        dx, dy = ex - x0, ey - y0
        d = math.hypot(dx, dy)
        if d < 1e-9 or d > 2 * R - 1e-6:
            return None
        h = math.sqrt(R * R - d * d / 4.0)
        sgn = -1 if b['mode'] == 2 else 1
        cx = (x0 + ex) / 2 + sgn * (-dy) / d * h
        cy = (y0 + ey) / 2 + sgn * dx / d * h
        return max(abs(math.hypot(px - cx, py - cy) - R) for px, py in pts)

    for k, b in enumerate(blocks):
        if b['comp'] not in (41, 42) or b['x0'] is None or b['mode'] not in (1, 2, 3):
            continue
        L = math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
        if L >= min_len:
            continue
        if not plain(b):
            log.append('  ! стр.%d: микро-кадр %.1f мкм со спецфункциями - не трогаю, исправить в CAM'
                       % (b['i'] + 1, L * 1000))
            continue
        # предыдущий оставшийся кадр того же контура
        q = k - 1
        while q >= 0 and blocks[q]['i'] in delete:
            q -= 1
        prv = blocks[q] if q >= 0 else None
        dev = None
        if prv is not None and plain(prv):
            pts = prv.setdefault('absorbed', []) + [(prv['x1'], prv['y1'])]
            dev = elem_dev(prv, b['x1'], b['y1'], pts)
        if dev is None or dev > max_dev:
            log.append('  ! стр.%d: микро-кадр %.1f мкм - не удалить без искажения контура (%s), исправить в CAM'
                       % (b['i'] + 1, L * 1000, 'нет подходящего соседа' if dev is None else '%.2f мкм' % (dev * 1000)))
            continue
        nxt = blocks[k + 1] if k + 1 < len(blocks) else None
        own_g = [g for g in b['g'] if g in (1, 2, 3)]
        if own_g and nxt is not None and not any(g in _NF_MOTION_G for g in nxt['g']):
            nnum, code, comment = _nf_split(lines[nxt['i']])
            lines[nxt['i']] = nnum + 'G%d ' % own_g[-1] + code.lstrip() + comment
            nxt['g'] = nxt['g'] + [float(own_g[-1])]
        prv['absorbed'] = pts
        set_end(prv, b['x1'], b['y1'])
        delete.add(b['i'])
        n_micro += 1
        log.append('  микро-кадр стр.%d (%.1f мкм) удалён, стр.%d продлена (откл. %.2f мкм)'
                   % (b['i'] + 1, L * 1000, prv['i'] + 1, dev * 1000))

    # --- внутренние дуги ---
    for b in blocks:
        if b['i'] in delete or b['mode'] not in (2, 3) or 'R' not in b['w'] or b['x0'] is None:
            continue
        if not ((b['comp'] == 42 and b['mode'] == 2) or (b['comp'] == 41 and b['mode'] == 3)):
            continue
        R = float(b['w']['R'])
        if R < 0:
            if abs(R) < rmin:
                log.append('  ! стр.%d: дуга >180° R%.5f меньше R_min - исправить в CAM' % (b['i'] + 1, R))
            continue
        if R >= rmin - 1e-9:
            continue
        chord = math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
        maxdev = max(maxdev, _nf_sagitta(R, chord) - _nf_sagitta(rmin, chord))
        nnum, code, comment = _nf_split(lines[b['i']])
        lines[b['i']] = nnum + re.sub(r'R-?\d*\.?\d+', 'R%.5f' % rmin, code, count=1) + comment
        n_arc += 1

    if n_arc:
        log.append('  внутренних дуг R<%.4f: %d -> R%.4f, недорез угла до %.2f мкм (в сторону инструмента, без перереза)'
                   % (rmin, n_arc, rmin, maxdev * 1000))
    if not (n_arc or n_micro):
        return None, log, (0, 0, 0.0)
    out = [l for i, l in enumerate(lines) if i not in delete]
    return ('\r\n' if crlf else '\n').join(out), log, (n_arc, n_micro, maxdev)

# ============================================================
# === ГЛАВНЫЙ КЛАСС ===
# ============================================================

class ErrAnc(Frame):
    def __init__(self, parent=None):
        Frame.__init__(self, parent)
        self.parent = parent
        self.file_vars = {}
        self.cached_paths = {}
        self.equidistant = 0.85
        self.settings = load_settings()
        self._poll_job = None       # id таймера after()
        self._poll_left = 0         # сколько опросов осталось
        self._poll_snap = None      # последний снимок папки
        self._busy = False          # идёт проверка столкновений
        self.cur_dirs = None        # (папка NC, папка JPG) последней проверки
        self.initUI()

    def initUI(self):
        self.master.title("Testing...")
        self.pack(fill=BOTH, expand=True)
        self.columnconfigure(0, weight=4)
        self.columnconfigure(1, weight=0)
        self.columnconfigure(2, weight=8)
        self.columnconfigure(3, weight=0)
        self.columnconfigure(4, weight=6)
        self.columnconfigure(5, weight=0)
        for r in range(11):
            self.rowconfigure(index=r, weight=1)
        Label(self, text='Подложка (Изображение):', font=("Calibri", 11, "bold")).grid(row=0, column=0, sticky=W, padx=5)
        Label(self, text='Лог проверки:', font=("Calibri", 11, "bold")).grid(row=0, column=2, sticky=W, padx=5)
        Label(self, text='Визуализация путей (G-код):', font=("Calibri", 11, "bold")).grid(row=0, column=4, sticky=W, padx=5)
        self.scale = 1.0
        self.init_canvas()
        self.canvas_widgets()
        self.com_widgets()
        self.makewidgets()
        self.plot_widgets()
        self.left_panel = Frame(self)
        self.left_panel.grid(row=11, column=0, columnspan=2, sticky=NSEW, padx=5, pady=5)
        f_btns = Frame(self.left_panel)
        f_btns.pack(anchor=W, fill=X, pady=2)
        Button(f_btns, text='Open Dir', command=lambda: self.serchErr('')).pack(side=LEFT, padx=2)
        Label(f_btns, text='Enter:').pack(side=LEFT, padx=2)
        self.entr = Entry(f_btns, width=12, font=("Calibri", 11))
        self.entr.pack(side=LEFT, padx=2)
        Button(f_btns, text='✔', width=3, command=lambda: self.enter(self.entr.get())).pack(side=LEFT, padx=2)
        Button(f_btns, text='⚠ Столкновения', width=15, fg='red', command=self.check_intersections).pack(side=LEFT, padx=2)
        self.progress = Progressbar(f_btns, orient=HORIZONTAL, length=120, mode='determinate')
        self.progress.pack(side=LEFT, padx=5)
        Button(f_btns, text='Clear', width=8, command=self.clear).pack(side=RIGHT, padx=2)
        f_inp = Frame(self.left_panel)
        f_inp.pack(anchor=W, fill=X, pady=2)
        Label(f_inp, text='Replace:', bg='yellow').pack(side=LEFT, padx=2)
        self.repl = Entry(f_inp, width=12, font=("Calibri", 11))
        self.repl.pack(side=LEFT, padx=2)
        Button(f_inp, text='☼', width=3, command=self.settings_dialog).pack(side=RIGHT, padx=2)
        # коррекция G-кода (Cornering / Corner peaks) для всей папки NC
        self.fix_btn = Button(f_inp, text='⚒ Fix G-code', fg='darkgreen', command=self.fix_gcode)
        self.fix_btn.pack(side=RIGHT, padx=2)
        # статус опроса и кнопка остановки — рядом с настройками
        self.watch_lbl = Label(f_inp, text='', fg='blue', font=("Calibri", 9))
        self.watch_lbl.pack(side=RIGHT, padx=4)
        self.stop_btn = Button(f_inp, text='Стоп', width=5, command=self.stop_watch)
        # кнопка показывается только во время опроса (см. start_watch)
        f_act = Frame(self.left_panel)
        f_act.pack(anchor=W, fill=X, pady=2)
        Button(f_act, text='Angle', command=lambda: self.repls(self.entr.get(), 1)).pack(side=LEFT, padx=2)
        Button(f_act, text='ABS', command=lambda: self.repls(self.entr.get(), 3)).pack(side=LEFT, padx=2)
        Button(f_act, text='Height', command=lambda: self.repls(self.entr.get(), 2)).pack(side=LEFT, padx=2)
        Button(f_act, text='add Comp', command=lambda: self.repls(self.entr.get(), 4)).pack(side=LEFT, padx=2)
        Button(f_act, text='Quit', width=8, fg='red', command=self.quit).pack(side=RIGHT, padx=2)
        f_xml = Frame(self.left_panel)
        f_xml.pack(anchor=W, fill=X, pady=2)
        Label(f_xml, text='Compare XML:', bg='yellow', font=("Calibri", 9, "bold")).pack(side=LEFT, padx=2)
        self.displayA = Label(f_xml, text='...', bg='lightblue', justify='left', font=("Calibri", 9))
        self.displayA.pack(side=LEFT, padx=5, fill=X, expand=True)
        self.lbl = Label(self.left_panel, text="Ждемс...", bd=1, relief=SUNKEN, anchor=W)
        self.lbl.pack(fill=X, pady=[5, 0])
        self.right_panel = Frame(self)
        self.right_panel.grid(row=11, column=4, columnspan=2, sticky=NSEW, padx=5, pady=5)
        Label(self.right_panel, text="Файлы траекторий путей:", font=("Calibri", 9, "bold")).pack(anchor=W)
        self.check_canvas = Canvas(self.right_panel, height=95, bg='#f0f0f0', bd=2, relief=SUNKEN)
        self.check_scrollbar = Scrollbar(self.right_panel, orient=VERTICAL, command=self.check_canvas.yview)
        self.check_frame = Frame(self.check_canvas, bg='#f0f0f0')
        self.check_canvas.configure(yscrollcommand=self.check_scrollbar.set)
        self.check_scrollbar.pack(side=RIGHT, fill=Y)
        self.check_canvas.pack(side=LEFT, fill=BOTH, expand=True)
        self.check_canvas.create_window((0, 0), window=self.check_frame, anchor="nw")
        self.check_frame.bind("<Configure>", lambda e: self.check_canvas.configure(scrollregion=self.check_canvas.bbox("all")))
        self.check_canvas.bind("<Enter>", lambda _: self.check_canvas.focus_set())
        self.check_canvas.bind("<MouseWheel>", self.check_canvas_wheel)
        self.entr.bind("<Return>", lambda e: self.enter(self.entr.get()))

    def init_canvas(self):
        self.ybar = Scrollbar(self, orient=VERTICAL)
        self.xbar = Scrollbar(self, orient=HORIZONTAL)
        self.canvas = Canvas(self, width=550, height=550, bd=2, relief=SUNKEN)
        self.ybar.grid(row=1, column=1, rowspan=9, sticky=S+N)
        self.xbar.grid(row=10, column=0, sticky=E+W+N)
        self.canvas.grid(row=1, column=0, rowspan=9, ipadx=5, ipady=5, padx=5, pady=5, sticky=E+W+S+N)
        self.xbar.config(command=self.canvas.xview)
        self.ybar.config(command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.ybar.set, xscrollcommand=self.xbar.set)
        self.canvas_inner_frame = Frame(self.canvas)
        self.canvas.create_window(0, 0, anchor='nw', window=self.canvas_inner_frame)
        self.canvas.bind("<Enter>", lambda _: self.canvas.focus_set())
        self.canvas.bind('<MouseWheel>', self.wheel)
        self.canvas.bind("<ButtonPress-1>", lambda e: self.canvas.scan_mark(e.x, e.y))
        self.canvas.bind("<B1-Motion>", lambda e: self.canvas.scan_dragto(e.x, e.y, gain=1))

    def canvas_widgets(self, adr=''):
        if adr == '':
            adr = r"\\storage\Files\Soft\illustrator_var\404.jpg"
        try:
            self.image = Im.open(adr)
            k = 550 / self.image.width
            newW = int(self.image.width * k)
            newH = int(self.image.height * k)
            self.image = self.image.resize([newW, newH])
            self.img = ImageTk.PhotoImage(self.image)
            self.canvas.delete("img_tag")
            self.canvas.create_image(0, 0, image=self.img, anchor='nw', tags="img_tag")
            self.canvas.configure(scrollregion=self.canvas.bbox('all'))
        except Exception as e:
            print(f"Ошибка загрузки подложки: {e}")

    def makewidgets(self):
        sbar = Scrollbar(self, orient=VERTICAL)
        text = Text(self, relief=RIDGE, height=25, width=45)
        sbar.config(command=text.yview)
        text.config(yscrollcommand=sbar.set)
        sbar.grid(row=1, column=3, rowspan=9, sticky=S+N)
        text.grid(row=1, column=2, rowspan=9, ipadx=5, ipady=5, padx=5, pady=5, sticky=E+W+S+N)
        self.text = text

    def com_widgets(self):
        f_com = Frame(self)
        f_com.grid(row=11, column=2, padx=5, pady=5, sticky=NSEW)
        cbar_com = Scrollbar(f_com, orient=VERTICAL)
        text_com = Text(f_com, relief=RIDGE, height=6, width=45)
        cbar_com.config(command=text_com.yview)
        text_com.config(yscrollcommand=cbar_com.set)
        cbar_com.pack(side=RIGHT, fill=Y)
        text_com.pack(side=LEFT, fill=BOTH, expand=True)
        self.text_com = text_com

    def plot_widgets(self):
        self.plot_ybar = Scrollbar(self, orient=VERTICAL)
        self.plot_xbar = Scrollbar(self, orient=HORIZONTAL)
        self.plot_canvas = Canvas(self, bg='white', bd=2, relief=SUNKEN, width=750, height=550)
        self.plot_ybar.grid(row=1, column=5, rowspan=9, sticky=S+N)
        self.plot_xbar.grid(row=10, column=4, sticky=E+W+N)
        self.plot_canvas.grid(row=1, column=4, rowspan=9, ipadx=5, ipady=5, padx=5, pady=5, sticky=E+W+S+N)
        self.plot_xbar.config(command=self.plot_canvas.xview)
        self.plot_ybar.config(command=self.plot_canvas.yview)
        self.plot_canvas.configure(yscrollcommand=self.plot_ybar.set, xscrollcommand=self.plot_xbar.set)
        self.plot_canvas.bind("<ButtonPress-1>", self.start_pan)
        self.plot_canvas.bind("<B1-Motion>", self.pan)
        self.plot_canvas.bind("<Enter>", lambda _: self.plot_canvas.focus_set())
        self.plot_canvas.bind('<MouseWheel>', self.plot_wheel)

    def start_pan(self, event):
        self._pan_start_x = event.x
        self._pan_start_y = event.y

    def pan(self, event):
        dx = event.x - self._pan_start_x
        dy = event.y - self._pan_start_y
        self.plot_canvas.move("all", dx, dy)
        v = self._plot_view()
        v[1] += dx
        v[2] += dy
        self._pan_start_x = event.x
        self._pan_start_y = event.y

    def wheel(self, event):
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        if int(-1*(event.delta)) < 0: self.scale -= 0.1
        else: self.scale += 0.1
        self.redraw(x, y)

    def plot_wheel(self, event):
        x = self.plot_canvas.canvasx(event.x)
        y = self.plot_canvas.canvasy(event.y)
        factor = 1.1 if event.delta > 0 else 0.9
        self.plot_canvas.scale("all", x, y, factor, factor)
        v = self._plot_view()
        v[0] *= factor
        v[1] = x + factor * (v[1] - x)
        v[2] = y + factor * (v[2] - y)
        self.plot_canvas.configure(scrollregion=self.plot_canvas.bbox('all'))

    def _plot_view(self):
        """Текущий зум/сдвиг графика: [масштаб, сдвиг_x, сдвиг_y]."""
        if not hasattr(self, '_view'):
            self._view = [1.0, 0.0, 0.0]
        return self._view

    def check_canvas_wheel(self, event):
        self.check_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def redraw(self, x=0, y=0):
        if hasattr(self, 'image') and self.image:
            iw, ih = self.image.size
            size = int(iw * self.scale), int(ih * self.scale)
            self.img = ImageTk.PhotoImage(self.image.resize(size))
            self.canvas.delete("img_tag")
            self.canvas.create_image(0, 0, image=self.img, anchor='nw', tags="img_tag")
            self.canvas.configure(scrollregion=self.canvas.bbox('all'), yscrollcommand=self.ybar.set, xscrollcommand=self.xbar.set)

    def settext(self, text='', colo=0):
        self.text.tag_config("here", foreground="red")
        self.text_com.tag_config("comma", foreground="red")
        self.text_com.tag_config("comma2", foreground="green")
        self.text.tag_config("XMLhere", background="yellow")
        self.text.tag_config("PPC", foreground="red", background="yellow")
        self.text.tag_config("info", foreground="blue")
        self.text.tag_config("good", foreground="green")
        self.text.tag_config("intersect", foreground="red", background="yellow")
        if colo == 1: self.text.insert(END, text+'\n', "here")
        elif colo == 2: self.text.insert(END, text+'\n', "XMLhere")
        elif colo == 3: self.text.insert(END, text+'\n', "PPC")
        elif colo == 4: self.text.insert(END, text+'\n', "info")
        elif colo == 5: self.text.insert(END, text+'\n', "intersect")
        elif colo == 6: self.text.insert(END, text, "good")
        elif colo == 7: self.text.insert(END, text, "info")
        else: self.text.insert(END, text+'\n')
        self.text.focus()

    def gettext(self): return self.text.get('1.0', END+'-1c')

    def openDir(self):
        global mark
        if len(sys.argv) < 2:
            self.help()
            mark = True
            dirname = askdirectory(mustexist=True, title='Please select a directory')
        else: dirname = sys.argv[1]
        dirname = os.path.normpath(dirname)
        self.lbl.config(text=dirname)
        self.puts("You chose %s" % dirname)
        self.puts('='*30)
        self.puts()
        return dirname

    def puts(self, txt='', colo=0):
        global mark
        if mark: self.settext(txt, colo)
        else:
            if colo == 1: print('Error: '+txt)
            elif colo == 2 or colo == 3: print('XML Error: '+txt)
            else: print(txt)

    def displ(self, anXML, hiXML, comment='gnr'):
        if getattr(self, 'cutXML', 'false') == 'true': cut = 'нестандартный'
        else: cut = 'обычный'
        if getattr(self, 'rll', 'false') == 'true': cut += '\nЗакаляем сталь'
        if getattr(self, 'angPlus', 'false') == 'true': cut += '\nРазновысотный'
        self.displayA.config(text='An: {}  Hi: {}  ({})'.format(anXML, hiXML, cut.replace('\n', ', ')))

    def ini(self, partentName):
        path_ini = os.path.normpath((r"\\storage\Files\Soft\illustrator_var\anctor.xml"))
        try:
            ini_tree = parse(path_ini)
            com_ini = ''
            for childs in ini_tree.findall('firm'):
                com_ini = childs.find('comm').text
                name = childs.get('name')
                if name == partentName:
                    self.text_com.insert(END, com_ini+'\n', "comma")
        except: self.text_com.insert(END, 'No such file!\n'+ path_ini, "comma")

    def XMLP(self, dir):
        norm_dir = os.path.normpath(dir)
        parts = norm_dir.split(os.sep)
        nc_idx = -1
        for idx, part in enumerate(parts):
            if '-NC' in part.upper():
                nc_idx = idx
                break
        if nc_idx != -1:
            hereDir = os.sep.join(parts[:nc_idx])
        else:
            hereDir = norm_dir[:norm_dir.rfind('-NC\\')]
            hereDir = hereDir[:hereDir.rfind('\\')]
        namberFile = 'specification_'+hereDir[hereDir.rfind('\\')+1:]+'.xml'
        anXML, hiXML = "0", "0"
        try:
            xmlFile = os.path.join(hereDir+'\\XML', namberFile)
            tree = parse(xmlFile)
            for height in tree.findall('ВысотаНожа'): hiXML = height.text
            for anl in tree.findall('УголЗаточкиКромки'): anXML = anl.text
            for cut in tree.findall('ТонкийНож'): self.cutXML = cut.text
            for rll in tree.findall('ЛазернаяЗакалка'): self.rll = rll.text
            for angPlus in tree.findall('НесколькоВысотКромки'): self.angPlus = angPlus.text
            comment = tree.getroot().attrib.get('КомментарийКонтрагента', '')
            comment2 = tree.getroot().attrib.get('Комментарий', '')
            parName = tree.getroot().attrib.get('Покупатель', '')
            self.text_com.delete('1.0', END)
            self.master.title(parName)
            self.ini(parName)
            self.text_com.insert(END, comment+'\n', "comma2")
            self.text_com.insert(END, comment2+'\n', "comma")
            if len(sys.argv) < 2: self.displ(anXML, hiXML, comment2)
        except Exception as e: self.puts('No such file "%s"! or error: %s' % (namberFile, e))
        return anXML, hiXML

    def serchErr(self, tDir, resolved=None):
        global mark
        allanc = []
        self.equidistant = 0.85
        from_dialog = (tDir == '' and not resolved)   # Open Dir — без автопроверки
        if resolved:                      # повторная проверка из опроса папки
            tDir, pathJPGs = resolved
            self.help()
            mark = True
        elif tDir == '':
            tDir = self.openDir()
            norm_path = os.path.normpath(tDir)
            parts = norm_path.split(os.sep)
            nc_idx = -1
            for idx, part in enumerate(parts):
                if '-NC' in part.upper():
                    nc_idx = idx
                    break
            if nc_idx != -1:
                hDir = parts[nc_idx].upper().replace('-NC', '')
                pathJPGs = os.sep.join(parts[:nc_idx] + ['JPG'])
            else:
                hDir = os.path.basename(norm_path)
                pathJPGs = os.path.dirname(norm_path) + "\\JPG"
            self.entr.delete(0, END)
            self.entr.insert(0, hDir)
            self.entr.select_range(0, 'end')
        else:
            self.help()
            mark = True
            pathJPGs = "\\\\storage\\Zakaz\\" + tDir[0:-3]+"000-"+ tDir[0:-3]+"999\\"+tDir+"\\"+"JPG"
            tDir = "\\\\storage\\Zakaz\\" + tDir[0:-3]+"000-"+ tDir[0:-3]+"999\\"+tDir+"\\"+tDir+"-NC"
        self.cur_dirs = (tDir, pathJPGs)
        self.lbl.config(text=tDir)
        self.puts("You chose %s" % tDir)
        self.puts('='*30)
        self.puts()
        if os.path.exists(tDir):
            for fileHere in os.listdir(tDir):
                if fileHere == [] or not fileHere.endswith('.anc'): continue
                allanc.append(os.path.join(tDir, fileHere))
        if os.path.exists(pathJPGs):
            for pathJPG in os.listdir(pathJPGs):
                if pathJPG == [] or not pathJPG.endswith('.jpg'): continue
                jpg = os.path.join(pathJPGs, pathJPG)
                self.canvas_widgets(jpg)
                break
        angleXML, heightXML = self.XMLP(tDir)
        prev_vars = {k: v.get() for k, v in self.file_vars.items()}  # сохранить галки при повторной проверке
        for widget in self.check_frame.winfo_children(): widget.destroy()
        self.file_vars = {}
        self.cached_paths = {}
        self.g_min_x, self.g_max_x = float('inf'), float('-inf')
        self.g_min_y, self.g_max_y = float('inf'), float('-inf')
        for files in allanc:
            fl = files[files.rfind('\\')+1:]
            angle = fl.split('_')
            mr = fl[fl.rfind('_')+1:fl.rfind('.')]
            i, j = 0, 0
            LSD = False
            EOFP = False
            namber_cut = 0
            compesation_cut = 0
            Drill = False
            drill_points = set()
            ToolCompMode = False
            self.fileR = False
            self.puts(files)
            if files.find('_R.anc') > -1 and files.find('revers') == -1 : self.fileR = True
            g0_moves = []
            pending_g0 = []
            cut_paths = []
            current_cut = []
            current_x, current_y = 0.0, 0.0
            current_mode = 0
            cutting_started = False
            try:
                with open(files, 'r', encoding='utf-8', errors='ignore') as f:
                    for line in f:
                        g_match = re.search(r'\bG0*([0-3])\b', line, re.IGNORECASE)
                        if g_match:
                            current_mode = int(g_match.group(1))
                        match_x = re.search(r'[X]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE)
                        match_y = re.search(r'[Y]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE)
                        match_i = re.search(r'[I]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE) or re.search(r'[A]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE)
                        match_j = re.search(r'[J]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE) or re.search(r'[B]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE)
                        match_r = re.search(r'[R]\s*([+-]?\d*\.?\d+)', line, re.IGNORECASE)
                        new_x = float(match_x.group(1)) if match_x else current_x
                        new_y = float(match_y.group(1)) if match_y else current_y
                        has_pos_change = (match_x is not None or match_y is not None)
                        if current_mode == 0:
                            if has_pos_change and (current_x != new_x or current_y != new_y):
                                if cutting_started:
                                    pending_g0.append((current_x, current_y, new_x, new_y))
                                if len(current_cut) >= 2:
                                    cut_paths.append(current_cut)
                                current_cut = []
                                current_x, current_y = new_x, new_y
                        elif current_mode in (1, 2, 3):
                            if pending_g0:
                                for gx1, gy1, gx2, gy2 in pending_g0:
                                    g0_moves.append((gx1, gy1, gx2, gy2))
                                    self.g_min_x = min(self.g_min_x, gx1, gx2)
                                    self.g_max_x = max(self.g_max_x, gx1, gx2)
                                    self.g_min_y = min(self.g_min_y, gy1, gy2)
                                    self.g_max_y = max(self.g_max_y, gy1, gy2)
                                pending_g0 = []
                            cutting_started = True
                            if current_mode == 1:
                                if has_pos_change:
                                    if not current_cut:
                                        current_cut.append((current_x, current_y))
                                    current_cut.append((new_x, new_y))
                                    self.g_min_x = min(self.g_min_x, current_x, new_x)
                                    self.g_max_x = max(self.g_max_x, current_x, new_x)
                                    self.g_min_y = min(self.g_min_y, current_y, new_y)
                                    self.g_max_y = max(self.g_max_y, current_y, new_y)
                                    current_x, current_y = new_x, new_y
                            elif current_mode in (2, 3):
                                is_cw = (current_mode == 2)
                                cx, cy = None, None
                                if match_r:
                                    r_val = float(match_r.group(1))
                                    cx, cy = get_arc_center_from_r(current_x, current_y, new_x, new_y, r_val, is_cw)
                                elif match_i or match_j:
                                    i_val = float(match_i.group(1)) if match_i else 0.0
                                    j_val = float(match_j.group(1)) if match_j else 0.0
                                    cx_rel, cy_rel = current_x + i_val, current_y + j_val
                                    r1_rel = math.hypot(current_x - cx_rel, current_y - cy_rel)
                                    r2_rel = math.hypot(new_x - cx_rel, new_y - cy_rel)
                                    cx_abs, cy_abs = i_val, j_val
                                    r1_abs = math.hypot(current_x - cx_abs, current_y - cy_abs)
                                    r2_abs = math.hypot(new_x - cx_abs, new_y - cy_abs)
                                    if abs(r1_abs - r2_abs) < abs(r1_rel - r2_rel) and r1_abs > 0.01:
                                        cx, cy = cx_abs, cy_abs
                                    else:
                                        cx, cy = cx_rel, cy_rel
                                if cx is not None and cy is not None:
                                    arc_pts = generate_arc_points(current_x, current_y, new_x, new_y, cx, cy, is_cw)
                                    if not current_cut:
                                        current_cut.append((current_x, current_y))
                                    for px, py in arc_pts:
                                        current_cut.append((px, py))
                                        self.g_min_x = min(self.g_min_x, px)
                                        self.g_max_x = max(self.g_max_x, px)
                                        self.g_min_y = min(self.g_min_y, py)
                                        self.g_max_y = max(self.g_max_y, py)
                                else:
                                    if not current_cut:
                                        current_cut.append((current_x, current_y))
                                    current_cut.append((new_x, new_y))
                                    self.g_min_x = min(self.g_min_x, current_x, new_x)
                                    self.g_max_x = max(self.g_max_x, current_x, new_x)
                                    self.g_min_y = min(self.g_min_y, current_y, new_y)
                                    self.g_max_y = max(self.g_max_y, current_y, new_y)
                                current_x, current_y = new_x, new_y
                        if 'SSDE[SD.WZRec.UD.Ed[1].Geo.Ang' in line:
                            angl = line[line.rfind('=')+2: line.rfind(']')]
                            k = 0
                            if len(angle) > 1 and angle[1] != angl: k = 1
                            if angl != angleXML: k += 2
                            self.puts('Angle = %s' % angl, k)
                        if 'ProgDieHeight' in line:
                            hi = line[line.rfind('=')+2: line.rfind(']')]
                            if hi != heightXML: self.puts('Height = %s' % hi, 2)
                            else: self.puts('Height = %s' % hi, 0)
                        if 'SSDE[SD.USR.ToolData.ProgToolEquidistant' in line:
                            eq_str = line[line.rfind('=')+2: line.rfind(']')].strip()
                            if '/' in eq_str:
                                parts_eq = eq_str.split('/')
                                try:
                                    self.equidistant = float(parts_eq[0]) / float(parts_eq[1])
                                except:
                                    pass
                            else:
                                try:
                                    self.equidistant = float(eq_str)
                                except:
                                    pass
                        if 'ZPosDiaMeas' in line:
                            dp = line[line.rfind('(')+1: line.rfind(']')-1]
                            if dp == '0.25' : nx = 6
                            else : nx = 7
                            if getattr(self, 'cutXML', 'false') == 'true':
                                cutx = 'нестандартный'
                                nt = 1
                            else:
                                cutx = 'обычный'
                                nt = 0
                            self.puts(f'Depth = {dp}',nx)
                            self.puts(f', {cutx} нож', nt)
                        if 'Altitude' in line: i += 1
                        if 'TOOL DATAS' in line: j += 1
                        if 'Begin of Contour' in line: EOFP = True
                        if 'Begin of Loop' in line and EOFP:
                            LSD = False
                            EOFP = False
                        if 'PREPART' in line:
                            namber_cut += 1
                            compesation_cut = 1
                        if 'G42' in line or 'G41' in line: compesation_cut = 0
                        if (';210,' in line or ';211,' in line) and 'G1' in line and 'Z' in line:
                            Drill = True
                            drill_points.add((round(new_x, 3), round(new_y, 3)))
                        if 'ToolCompMode = 1' in line: ToolCompMode = line[line.find('ToolCompMode =')+15:line.find(']')]
                if len(current_cut) >= 2:
                    cut_paths.append(current_cut)
            except Exception as e:
                self.puts(f"Ошибка парсинга файла: {e}", 1)
            self.cached_paths[files] = {
                'g0': g0_moves,
                'cut': cut_paths
            }
            # --- разбор PART'ов для проверки лидов ---
            try:
                lead_parts, lead_eq = parse_anc_parts(files)
            except Exception as e:
                lead_parts, lead_eq = [], None
                self.puts(f"Ошибка разбора лидов: {e}", 1)
            self.cached_paths[files]['parts'] = lead_parts
            self.cached_paths[files]['eq'] = lead_eq
            is_default_active = fl.lower().endswith('_all_r.anc')
            var = BooleanVar(value=prev_vars.get(files, is_default_active))
            self.file_vars[files] = var
            cb = Checkbutton(self.check_frame, text=fl, variable=var, bg='#f0f0f0', fg='black',
                             selectcolor='white', activebackground='#e0e0e0', font=("Calibri", 10),
                             command=self.redraw_plots)
            cb.pack(anchor=W, padx=5, pady=1)
            cb.bind("<MouseWheel>", self.check_canvas_wheel)
            if ToolCompMode: self.puts('Не включена компенсация (G41/42) = %s' % ToolCompMode, 3)
            if compesation_cut: self.puts("Путей = %s без компенсации" % namber_cut, compesation_cut)
            if i > 0:
                if mr == 'M':
                    self.puts('Программа с измерениями')
                    self.puts('Количество измерений = %s' % i)
                else:
                    self.puts('Программа с измерениями', 1)
                    self.puts('Количество измерений = %s' % i, 1)
            #else:
            #    if mr == 'R': self.puts('Программа без измерений')
            #    else: self.puts('Программа без измерений', 0)
            if j > 1: self.puts('Label Tool Data (Много инструментов в одной программе)', 3)
            if LSD: self.puts('Label Shape Data (Хз)', 3)
            drill_count = len(drill_points)
            if Drill:
                self.puts(f'Есть сверление точек ({drill_count} шт.)', 4)
            elif getattr(self, 'rll', 'false') == 'true' and self.fileR:
                self.puts('Нет точек для сверления', 3)
            self.puts('-'*30)
            self.puts()

        self.puts(f'Радиус инструмента (эквидистанта) = {self.equidistant}', 4)
        self.puts('='*30)

        self.redraw_plots()
        self.entr.focus()
        if mark and not from_dialog and self.settings.get('auto_collisions'):
            self.update_idletasks()
            self.auto_collisions()

    def auto_collisions(self):
        """Автопроверка столкновений только для *_R.anc без 'revers'."""
        only = {f for f in self.cached_paths if is_auto_collision_file(f)}
        if not only:
            self.puts('Автопроверка столкновений: нет файлов *_R.anc', 4)
            return
        self.check_intersections(only)

    def redraw_plots(self):
        self.plot_canvas.delete("path")
        self.plot_canvas.delete("intersection")

        self._view = [1.0, 0.0, 0.0]
        if not self.cached_paths or self.g_min_x == float('inf'): return

        w, h, pad = 750, 550, 40
        dx = self.g_max_x - self.g_min_x if self.g_max_x != self.g_min_x else 1
        dy = self.g_max_y - self.g_min_y if self.g_max_y != self.g_min_y else 1
        scale = min((w - pad * 2) / dx, (h - pad * 2) / dy)

        for file_path, path_data in self.cached_paths.items():
            if self.file_vars[file_path].get():
                fl_lower = os.path.basename(file_path).lower()
                if '_revers' in fl_lower:
                    color = 'pink'
                    line_width = 1
                elif '_corner' in fl_lower:
                    color = 'green'
                    line_width = 1
                elif '_all' in fl_lower:
                    color = 'red'
                    line_width = 1
                elif '_sv' in fl_lower:
                    color = 'yellow'
                    line_width = 1
                else:
                    color = '#0022AA'
                    line_width = 2
                for x1, y1, x2, y2 in path_data.get('g0', []):
                    sx1 = pad + (x1 - self.g_min_x) * scale
                    sy1 = h - pad - (y1 - self.g_min_y) * scale
                    sx2 = pad + (x2 - self.g_min_x) * scale
                    sy2 = h - pad - (y2 - self.g_min_y) * scale
                    self.plot_canvas.create_line(
                        sx1, sy1, sx2, sy2,
                        fill='#888888', dash=(3, 3), width=1,
                        arrow=LAST, arrowshape=(6, 8, 3), tags="path"
                    )
                for points in path_data.get('cut', []):
                    if len(points) < 2: continue
                    scaled_coords = []
                    for x, y in points:
                        sx = pad + (x - self.g_min_x) * scale
                        sy = h - pad - (y - self.g_min_y) * scale
                        scaled_coords.extend([sx, sy])
                    self.plot_canvas.create_line(
                        scaled_coords,
                        fill=color, width=line_width,
                        arrow=LAST, arrowshape=(8, 10, 4), tags="path"
                    )

        self.plot_canvas.configure(scrollregion=self.plot_canvas.bbox('all'))

    def check_intersections(self, only=None):
        self._busy = True
        try:
            self._check_intersections(only)
        finally:
            self._busy = False

    def _check_intersections(self, only=None):
        """Столкновения: контур-контур разных PART (светло-зелёный) и врезание лидов (тёмно-зелёный)."""
        self.plot_canvas.delete("intersection")
        if not self.cached_paths or self.g_min_x == float('inf'):
            self.puts("Нет данных для проверки", 4)
            return

        w, h, pad = 750, 550, 40
        dx = (self.g_max_x - self.g_min_x) or 1
        dy = (self.g_max_y - self.g_min_y) or 1
        scale = min((w - 2 * pad) / dx, (h - 2 * pad) / dy)

        vs, vx, vy = self._plot_view()

        def to_screen(x, y):
            sx = pad + (x - self.g_min_x) * scale
            sy = h - pad - (y - self.g_min_y) * scale
            return sx * vs + vx, sy * vs + vy

        def prog(i, n):
            self.progress['maximum'] = max(n, 1)
            self.progress['value'] = i
            self.update_idletasks()

        self.puts(f"--- Проверка столкновений (эквидистанта={self.equidistant:.4f}) ---", 4)
        self.update()

        green = []   # (x, y, file, part, target_part, depth, r)
        red = []     # (x, y, file, part, target_part, kind, depth, r)

        for file_path, data in self.cached_paths.items():
            if only is not None:                  # автопроверка: свой список файлов
                if file_path not in only:
                    continue
            else:
                var = self.file_vars.get(file_path)
                if var is not None and not var.get():
                    continue
            parts = data.get('parts') or []
            r = data.get('eq') or self.equidistant
            radii = sorted({round(p.get('eq') or r, 4) for p in parts})
            n_green = n_red = 0
            # 1. контур срезает кромку другого PART (светло-зелёный)
            for pi, pj, depth, (x, y) in find_contour_collisions(parts, r, progress=prog):
                green.append((x, y, file_path, pi, pj, depth, _part_r(parts[pi], r)))
                n_green += 1
            # 2. врезание лидов (тёмно-зелёный)
            for pi, pj, kind, depth, (x, y) in find_lead_gouges(parts, r, progress=prog):
                red.append((x, y, file_path, pi, pj, kind, depth, _part_r(parts[pi], r)))
                n_red += 1
            self.puts(f"{os.path.basename(file_path)}: PART={len(parts)}, "
                      f"радиус={', '.join(str(v) for v in radii) or '?'}, "
                      f"пути={n_green}, лиды={n_red}", 4)
            if parts and n_green > len(parts) * 0.3:
                self.puts("  Подозрительно много пересечений — проверьте радиус "
                          "(ProgToolEquidistant) в этом файле", 3)

        self.progress['value'] = 0

        # ---------- Отрисовка ----------
        size = 10
        for x, y, f, pi, pj, depth, r in green:
            sx, sy = to_screen(x, y)
            self.plot_canvas.create_rectangle(sx - size, sy - size, sx + size, sy + size,
                                              outline='#32CD32', width=2, tags="intersection")
            self.plot_canvas.create_text(sx, sy - size - 6, text=f"PART{pi + 1}/{pj + 1} {depth:.2f}",
                                         fill='#32CD32', font=("Calibri", 8, "bold"), tags="intersection")
        for x, y, f, pi, pj, kind, depth, r in red:
            sx, sy = to_screen(x, y)
            rr = max(r * scale * vs, 6)
            self.plot_canvas.create_oval(sx - rr, sy - rr, sx + rr, sy + rr,
                                         outline='#006400', width=2, tags="intersection")
            self.plot_canvas.create_text(sx, sy - rr - 6, text=f"PART{pi + 1} {depth:.2f}",
                                         fill='#006400', font=("Calibri", 8, "bold"), tags="intersection")

        # ---------- Лог ----------
        MAX_LOG = 40
        if green:
            self.puts(f"Пересечения путей: {len(green)}", 5)
            for k, (x, y, f, pi, pj, depth, r) in enumerate(sorted(green, key=lambda g: -g[5])[:MAX_LOG], 1):
                self.puts(f"  #{k}: {os.path.basename(f)} PART{pi + 1} -> PART{pj + 1}: "
                          f"врезание {depth:.3f} мм, точка=({x:.2f}, {y:.2f})", 5)
            if len(green) > MAX_LOG:
                self.puts(f"  ... и ещё {len(green) - MAX_LOG}", 5)
        else:
            self.puts("Пересечений путей не найдено", 4)
        if red:
            self.puts(f"Врезания лидов: {len(red)}", 5)
            for k, (x, y, f, pi, pj, kind, depth, r) in enumerate(sorted(red, key=lambda t: -t[6])[:MAX_LOG], 1):
                who = 'свой контур' if pi == pj else f'PART{pj + 1}'
                lead = 'лид-вход' if kind == 'lead_in' else 'лид-выход'
                self.puts(f"  #{k}: {os.path.basename(f)} PART{pi + 1} {lead} -> {who}: "
                          f"врезание {depth:.3f} мм, точка=({x:.2f}, {y:.2f})", 5)
            if len(red) > MAX_LOG:
                self.puts(f"  ... и ещё {len(red) - MAX_LOG}", 5)
        else:
            self.puts("Лиды в порядке", 4)

        self.plot_canvas.configure(scrollregion=self.plot_canvas.bbox('all'))
        self.puts("--- Проверка завершена ---", 4)

    def _point_seg_dist(self, px, py, x1, y1, x2, y2):
        """Расстояние от точки до отрезка."""
        dx, dy = x2 - x1, y2 - y1
        len_sq = dx * dx + dy * dy
        if len_sq < 1e-12:
            return math.hypot(px - x1, py - y1), (x1, y1)
        t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / len_sq))
        nx, ny = x1 + t * dx, y1 + t * dy
        return math.hypot(px - nx, py - ny), (nx, ny)

    def infobox(self, e=0, title='Настройки', text=ver, *args): return showinfo(title, text)
    def errorbox(self, text): showerror('Error!', text)
    def question(self, title, text, *args): return askyesno(title, text)
    def notdone(self): showerror('Not implemented', 'Option not available')
    def quit(self):
        if self.question('Verify quit', 'Are you sure you want to quit?'): Frame.quit(self)
    def help(self):
        self.text.delete('1.0', END)
        self.text_com.delete('1.0', END)
        self.entr.select_range(0, 'end')
        self.canvas_widgets('')
        self.lbl.config(text='Ждемс...')
    def clear(self):
        self.stop_watch()
        self.help()
        self.entr.delete(0, 'end')
        self.repl.delete(0, 'end')
        if hasattr(self, 'plot_canvas'): self.plot_canvas.delete("all")
        for widget in self.check_frame.winfo_children(): widget.destroy()
        self.file_vars, self.cached_paths = {}, {}
        self.entr.focus()
    def enter(self, f):
        self.stop_watch()
        self.cur_dirs = None
        if f == '':
            self.serchErr('')             # Open Dir — без опроса
        else:
            self.serchErr(f)
            self.start_watch()            # опрос только для ручного ввода номера

    # ---------- опрос папки ----------
    def start_watch(self):
        """После проверки следим за папкой: N опросов с интервалом T сек."""
        n = self.settings.get('poll_count', 0)
        t = self.settings.get('poll_interval', 0)
        if not self.cur_dirs or n <= 0 or t <= 0:
            return
        self._poll_left = n
        self._poll_snap = dir_snapshot(self.cur_dirs[0])
        self.stop_btn.pack(side=RIGHT, padx=2, before=self.watch_lbl)
        self._update_watch_lbl()
        self._poll_job = self.after(t * 1000, self._poll_tick)

    def stop_watch(self):
        if self._poll_job is not None:
            try: self.after_cancel(self._poll_job)
            except Exception: pass
        self._poll_job = None
        self._poll_left = 0
        self.watch_lbl.config(text='')
        self.stop_btn.pack_forget()

    def _update_watch_lbl(self, changed=False):
        n = self.settings.get('poll_count', 0)
        done = n - self._poll_left
        txt = 'Опрос {}/{}'.format(done, n)
        if changed: txt += ' — обновлено'
        self.watch_lbl.config(text=txt)

    def _poll_tick(self):
        self._poll_job = None
        t = self.settings.get('poll_interval', 1)
        if self._busy:                    # идёт проверка столкновений — подождать
            self._poll_job = self.after(t * 1000, self._poll_tick)
            return
        self._poll_left -= 1
        snap = dir_snapshot(self.cur_dirs[0])
        changed = snap != self._poll_snap
        if changed:
            self._poll_snap = snap
            left = self._poll_left
            self.serchErr('', resolved=self.cur_dirs)   # то же, что нажать Ввод
            self._poll_left = left
        if self._poll_left > 0:
            self._update_watch_lbl(changed)
            self._poll_job = self.after(t * 1000, self._poll_tick)
        else:
            self.stop_watch()
            self.watch_lbl.config(text='Опрос завершён')

    # ---------- окно настроек ----------
    def settings_dialog(self):
        win = Toplevel(self)
        win.title('Настройки')
        win.resizable(False, False)
        win.transient(self.winfo_toplevel())
        Label(win, text=ver, font=("Calibri", 11, "bold")).grid(row=0, column=0, columnspan=2, pady=(8, 6), padx=10)
        Label(win, text='Количество опросов папки:').grid(row=1, column=0, sticky=W, padx=10, pady=3)
        cnt = Spinbox(win, from_=0, to=1000, width=7)
        cnt.delete(0, END); cnt.insert(0, self.settings['poll_count'])
        cnt.grid(row=1, column=1, padx=10, pady=3)
        Label(win, text='Интервал опроса, сек:').grid(row=2, column=0, sticky=W, padx=10, pady=3)
        itv = Spinbox(win, from_=1, to=3600, width=7)
        itv.delete(0, END); itv.insert(0, self.settings['poll_interval'])
        itv.grid(row=2, column=1, padx=10, pady=3)
        Label(win, text='0 опросов — опрос выключен', fg='gray').grid(row=3, column=0, columnspan=2, padx=10)
        auto_var = IntVar(value=1 if self.settings.get('auto_collisions') else 0)
        Checkbutton(win, text='Автопроверка столкновений (*_R.anc, без revers)',
                    variable=auto_var).grid(row=4, column=0, columnspan=2, sticky=W, padx=10, pady=(6, 0))
        Label(win, text='Fix G-code: один R_min на основные программы', font=("Calibri", 10, "bold")).grid(row=5, column=0, columnspan=2, sticky=W, padx=10, pady=(8, 0))
        fx = Frame(win); fx.grid(row=6, column=0, columnspan=2, sticky=W, padx=10)
        fix_e = {}
        for r, (title, k) in enumerate((('Площадка: макс. + к номиналу, мм', 'fix_dtip'),
                                        ('Макс. угол заточки, °', 'fix_ang'),
                                        ('Страховка, мм', 'fix_safety'),
                                        ('R_min основных вручную, мм (0 = авто)', 'fix_rmin'))):
            Label(fx, text=title + ':').grid(row=r, column=0, sticky=W)
            e = Entry(fx, width=7); e.insert(0, '%g' % self.settings.get(k, 0))
            e.grid(row=r, column=1, padx=4, pady=2); fix_e[k] = e
        Label(fx, text='Программы мелких углов (в имени, через запятую):').grid(row=4, column=0, sticky=W)
        corner_e = Entry(fx, width=12); corner_e.insert(0, self.settings.get('fix_corner_mask', 'corner'))
        corner_e.grid(row=4, column=1, padx=4, pady=2)
        Label(fx, text='Мин. радиус угла по чертежу (corner, не 3D), мм:').grid(row=6, column=0, sticky=W)
        e = Entry(fx, width=7); e.insert(0, '%g' % self.settings.get('fix_corner_rmin', 0.5))
        e.grid(row=6, column=1, padx=4, pady=2); fix_e['fix_corner_rmin'] = e
        Label(fx, text='Худший инструмент группы: площадка 0.40, бывает до 0.55 -> +0.15; точат до 90°.\n'
                       'Основные (черновые+чистовые) - один R_min; мелкие углы - свой, по corner-инструменту.',
              fg='gray', justify=LEFT).grid(row=5, column=0, columnspan=2, sticky=W)
        bak_var = IntVar(value=1 if self.settings.get('fix_backup', 1) else 0)
        Checkbutton(win, text='Сохранять оригиналы в подпапку ' + NF_BACKUP_DIR,
                    variable=bak_var).grid(row=7, column=0, columnspan=2, sticky=W, padx=10)

        def ok(e=None):
            try:
                n = int(cnt.get()); t = int(itv.get())
                if n < 0 or t < 1: raise ValueError
            except ValueError:
                showerror('Настройки', 'Введите целые числа: опросов ≥ 0, интервал ≥ 1', parent=win)
                return
            fixv = {}
            try:
                for k, e in fix_e.items():
                    v = float(e.get().replace(',', '.'))
                    lim = 180 if k == 'fix_ang' else 5
                    if not 0 <= v < lim: raise ValueError
                    fixv[k] = v
            except ValueError:
                showerror('Настройки', 'Fix G-code: значения в мм (0..5), угол 0..179°', parent=win)
                return
            self.settings['poll_count'] = n
            self.settings['poll_interval'] = t
            self.settings['auto_collisions'] = auto_var.get()
            self.settings.update(fixv)
            self.settings['fix_corner_mask'] = corner_e.get().strip()
            self.settings['fix_backup'] = bak_var.get()
            if not save_settings(self.settings):
                showerror('Настройки', 'Не удалось сохранить:\n' + SETTINGS_FILE, parent=win)
            win.destroy()
            self.entr.focus()

        bf = Frame(win); bf.grid(row=8, column=0, columnspan=2, pady=8)
        Button(bf, text='OK', width=10, command=ok).pack(side=LEFT, padx=4)
        Button(bf, text='Отмена', width=10, command=win.destroy).pack(side=LEFT, padx=4)
        win.bind('<Return>', ok)
        win.bind('<Escape>', lambda e: win.destroy())
        win.grab_set()
        cnt.focus_set()
    # ---------- коррекция G-кода ----------
    def _fix_target_dir(self):
        """Папка NC: последняя проверенная -> номер в поле Enter -> выбор вручную."""
        if self.cur_dirs and os.path.isdir(self.cur_dirs[0]):
            return self.cur_dirs[0]
        w = self.entr.get().strip()
        if w:
            d = "\\\\storage\\Zakaz\\" + w[0:-3] + "000-" + w[0:-3] + "999\\" + w + "\\" + w + "-NC"
            if os.path.isdir(d):
                return d
        d = askdirectory(mustexist=True, title='Папка с NC-программами для коррекции')
        return os.path.normpath(d) if d else None

    def fix_gcode(self):
        if self._busy:
            showinfo('Fix G-code', 'Дождитесь окончания текущей проверки.')
            return
        st = self.settings
        d = self._fix_target_dir()
        if not d:
            return
        try:   # только файлы в самой папке, без вложенных
            files = sorted(os.path.join(d, n) for n in os.listdir(d)
                           if n.lower().endswith('.anc') and os.path.isfile(os.path.join(d, n)))
        except OSError as e:
            showerror('Fix G-code', 'Нет доступа к папке:\n%s\n%s' % (d, e))
            return
        if not files:
            showinfo('Fix G-code', 'В папке нет файлов .anc:\n' + d)
            return

        backup = bool(st.get('fix_backup', 1))
        dtip, ang_max = st.get('fix_dtip', 0.15), st.get('fix_ang', 90)
        safety, rmin_manual = st.get('fix_safety', 0.03), st.get('fix_rmin', 0)
        bdir = os.path.join(d, NF_BACKUP_DIR)
        manifest = _nf_manifest(bdir) if os.path.isdir(bdir) else {}

        # --- проход 1: исходники (оригиналы, если файл - наша прошлая правка) и худший радиус ---
        cmask = st.get('fix_corner_mask', 'corner')
        items = []          # [path, name, cur, src, from_orig, группа]
        worst = {0: [], 1: [], 2: []}   # группа: 0 основные, 1 corner, 2 corner 3D -> [(r, name)]
        crmin = st.get('fix_corner_rmin', 0.5)
        pre_warns = []
        for path in files:
            name = os.path.basename(path)
            try:
                with open(path, 'rb') as f:
                    cur = f.read()
                bpath = os.path.join(bdir, name)
                from_orig = os.path.isfile(bpath) and manifest.get(name) == _nf_hash(cur)
                if from_orig:
                    with open(bpath, 'rb') as f:
                        src = f.read()
                else:
                    src = cur
                txt = src.decode('latin-1')
                # 3D определяется ТОЛЬКО по ToolType = 1; имя - лишь для сверки (человеческий фактор)
                is3d_txt, is3d_name = nc_is_3d(txt), 'corner3d' in name.lower()
                if is3d_txt:
                    grp = 2
                else:
                    grp = 1 if nc_is_corner(name, cmask) else 0
                if is3d_txt != is3d_name:
                    pre_warns.append('! %s: %s' % (name, 'ToolType = 1, но в имени нет corner3D - считаю 3D'
                                     if is3d_txt else 'в имени corner3D, но ToolType не 1 - считаю НЕ 3D'))
                items.append([path, name, cur, src, from_orig, grp])
                r = nc_worst_radius(txt, dtip, ang_max)
                if r is not None:
                    worst[grp].append((r, name))
            except Exception as e:
                showerror('Fix G-code', 'Не прочитать файл:\n%s\n%s' % (path, e))
                return
        rmins, hows, warns = {}, {}, list(pre_warns)
        for grp, title in ((0, 'Основные'), (1, 'Мелкие углы (%s)' % cmask), (2, 'Мелкие углы 3D (ToolType = 1)')):
            if not any(it[5] == grp for it in items):
                continue
            if grp == 0 and rmin_manual > 0:
                r, h = rmin_manual, 'задан вручную'
            elif grp == 1 and crmin > 0:
                r, h = crmin, 'мин. радиус угла по чертежу'
                for rw, nm in worst[1]:
                    if rw > crmin:
                        warns.append('! %s: радиус коррекции corner-инструмента с допуском заточки до %.3f > R%g - '
                                     'если площадку заточат с превышением, станок остановится на углах R%g' % (nm, rw, crmin, crmin))
            elif worst[grp]:
                r_max, n_max = max(worst[grp])
                r, h = r_max + safety, 'по %s: до %.4f + %.3f' % (n_max, r_max, safety)
            else:
                r, h = None, 'нет данных инструмента - не исправляются'
            rmins[grp] = None if r is None else math.ceil(r * 1e5 - 1e-6) / 1e5
            n = sum(1 for it in items if it[5] == grp)
            hows[grp] = '%s (%d): R_min %s, %s' % (title, n, '-' if r is None else '%.5f' % rmins[grp], h)

        msg = ('Папка:\n%s\n\nФайлов .anc: %d\n\n%s\n(площадка +%.3f, угол до %g°)\n'
               % (d, len(files), '\n'.join(hows[g] for g in (0, 1, 2) if g in hows), dtip, ang_max))
        if warns:
            msg += '\n' + '\n'.join(warns) + '\n'
        msg += ('\nОригиналы: %s (правка всегда от оригинала)\n' % NF_BACKUP_DIR) if backup else '\nОригиналы НЕ сохраняются!\n'
        msg += '\nИсправить файлы?'
        if not self.question('Fix G-code', msg):
            return

        # --- проход 2: правка всех файлов с одним R_min ---
        self._busy = True
        self.fix_btn.config(state=DISABLED)
        self.settext('')
        self.settext('=== Fix G-code: %s ===' % d, 4)
        for g in (0, 1, 2):
            if g in hows:
                self.settext(hows[g], 4)
        for w in warns:
            self.settext(w, 1)
        self.progress['maximum'] = len(items)
        self.progress['value'] = 0
        n_files = n_arcs = n_micro = n_err = n_rest = 0
        try:
            for k, (path, name, cur, src, from_orig, grp) in enumerate(items, 1):
                try:
                    bpath = os.path.join(bdir, name)
                    have_b = os.path.isfile(bpath)
                    if rmins.get(grp) is None:
                        self.settext(name + ': пропущен (нет данных инструмента)', 1)
                        continue
                    name_l = name + ('', ' [corner]', ' [corner 3D]')[grp]
                    new_text, log, (a, mc, dev) = nc_fix_text(src.decode('latin-1'), min_radius=rmins[grp])
                    out = src if new_text is None else new_text.encode('latin-1')
                    if out == cur:
                        log = [l for l in log if '!' in l or 'ВНИМАНИЕ' in l]   # правок нет - только предупреждения
                        self.settext(name_l + (': OK (уже исправлен под этот R_min)' if from_orig else ': OK'),
                                     6 if not log else 0)
                        if not log: self.settext('')
                    else:
                        bk_ok = from_orig
                        if backup and not from_orig:
                            os.makedirs(bdir, exist_ok=True)
                            if have_b and name not in manifest:
                                # старая копия без отметки - не трогаем, текущий файл берём как есть
                                self.settext('  ! в %s уже есть %s без отметки - копия не обновлена' % (NF_BACKUP_DIR, name), 1)
                            else:      # новый оригинал (или CAM перевыгрузил программу)
                                with open(bpath, 'wb') as f:
                                    f.write(cur)
                                bk_ok = True
                        tmp = path + '.fixtmp'
                        with open(tmp, 'wb') as f:
                            f.write(out)
                        os.replace(tmp, path)
                        if bk_ok:
                            manifest[name] = _nf_hash(out)
                        else:
                            manifest.pop(name, None)
                        if new_text is None:
                            n_rest += 1
                            self.settext('%s: восстановлен оригинал (правки не нужны)' % name_l, 4)
                        else:
                            n_files += 1; n_arcs += a; n_micro += mc
                            self.settext('%s: ИСПРАВЛЕН (дуг %d, микро-кадров %d)%s'
                                         % (name_l, a, mc, ' - от оригинала' if from_orig else ''), 1)
                    for l in log:
                        self.settext(l, 1 if '!' in l or 'ВНИМАНИЕ' in l else 0)
                except Exception as e:
                    n_err += 1
                    self.settext('%s: ОШИБКА %s' % (name, e), 5)
                self.progress['value'] = k
                self.update_idletasks()
            if os.path.isdir(bdir) and manifest:
                try: _nf_manifest(bdir, manifest)
                except Exception as e: self.settext('Не удалось записать %s: %s' % (NF_MANIFEST, e), 5)
        finally:
            self._busy = False
            self.fix_btn.config(state=NORMAL)
            self.progress['value'] = 0      # градусник общий со «Столкновениями» - сбрасываем
            self.update_idletasks()
        self.settext('')
        self.settext('ИТОГО: файлов %d, исправлено %d (дуг %d, микро-кадров %d), восстановлено %d, ошибок %d'
                     % (len(items), n_files, n_arcs, n_micro, n_rest, n_err), 4)
        if self._poll_job is not None and self.cur_dirs and self.cur_dirs[0] == d:
            self._poll_snap = dir_snapshot(d)   # свои правки не считаем изменением папки
        self.text.see(END)

    def repls(self, wDir, btn):
        allanc = []
        if wDir == '': return 0
        wDir = "\\\\storage\\Zakaz\\" + wDir[0:-3]+"000-"+ wDir[0:-3]+"999\\"+wDir+"\\"+wDir+"-NC"
        if os.path.exists(wDir):
            for fileHere in os.listdir(wDir):
                if fileHere == [] or not fileHere.endswith('.anc'): continue
                allanc.append(os.path.join(wDir, fileHere))
        for files in allanc:
            seeks = 0
            try:
                with open(files, "r+") as f:
                    my_lines = f.readlines()
                    for line in my_lines:
                        seeks += len(line)+1
                        if btn == 1 and 'SSDE[SD.WZRec.UD.Ed[1].Geo.Ang' in line:
                            temp = '        '; f.seek(seeks-10); f.write(temp)
                            f.seek(seeks-len(line)-1)
                            temp = line[:line.rfind("=")+2] + self.repl.get() + "]"
                            f.write(temp)
                        elif btn == 2 and 'ProgDieHeight' in line:
                            temp = '        '; f.seek(seeks-10); f.write(temp)
                            f.seek(seeks-len(line)-1)
                            temp = line[:line.rfind("=")+2] + self.repl.get() + "]"
                            f.write(temp)
                        elif btn == 3 and 'ABS(' in line:
                            temp = '        '; f.seek(seeks-10); f.write(temp)
                            f.seek(seeks-len(line)-1)
                            temp = line[:line.rfind("(")+1] + self.repl.get() + ")]"
                            f.write(temp)
                        elif btn == 4 and 'ToolCompMode' in line:
                            temp = '        '; f.seek(seeks-10); f.write(temp)
                            f.seek(seeks-len(line)-1)
                            temp = line[:line.rfind("=")] + "= 0]"
                            f.write(temp)
            except Exception as e: print(f"Ошибка модификации: {e}")
            if btn == 1:
                nfile = files[:files.find("_")+1]
                new_files = nfile + self.repl.get() + files[files.find("_", len(nfile), len(files)):]
                try: os.rename(files, new_files)
                except Exception as e: print(f"Ошибка переименования: {e}")
        self.entr.focus()

if __name__ == '__main__':
    if len(sys.argv) < 2:
        root = Tk()
        # под pythonw ошибки в кнопках иначе молча пропадают
        def _cb_error(t, v, tb):
            txt = ''.join(traceback.format_exception(t, v, tb))
            try:
                log = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'anctor_error.log')
                with open(log, 'a', encoding='utf-8') as f:
                    f.write(txt + '=' * 60 + '\n')
            except Exception:
                pass
            showerror('Anctor: ошибка', txt[-1500:])
        root.report_callback_exception = _cb_error
        root.geometry("1550x820")
        app = ErrAnc(root)
        root.mainloop()
    else:
        st = ErrAnc()
        st.serchErr()
        input('Press any key...')
