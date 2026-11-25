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
ver = 'Anctor V8.8'

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
DEFAULT_SETTINGS = {'poll_count': 10, 'poll_interval': 5, 'auto_collisions': 0, 'auto_fix': 0,
                    'fix_backup': 1,
                    # Fix G-code: ОДНО значение R_min на всю папку (одинаковая геометрия у всех программ)
                    'fix_dtip': 0.15,    # макс. превышение площадки (Tool-R) над номиналом, мм
                    'fix_ang': 90,       # макс. угол заточки, ° (если в программе меньше - берётся этот)
                    'fix_safety': 0.03,  # страховка, мм
                    'fix_radius': 1,     # коррекция малых внутренних радиусов (R_min): 1 вкл, 0 выкл
                    'fix_move_entry': 0, # переносить вход/выход контура из дуги на середину длинной прямой
                    'fix_rmin_all': 0.5, # мин. радиус углов макета для всех программ (кроме 3D), мм; 0 = по допускам
                    'fix_corner_mask': 'corner',   # программы доработки мелких углов (подстроки через запятую)
                    }
FLOAT_SETTINGS = ('fix_dtip', 'fix_ang', 'fix_safety', 'fix_rmin_all')
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


def _nf_lead(code, comment):
    """Вход/выход на контур: 12 / 13 / None. Старый постпроцессор - G12/G13 в кадре,
    новый - явная дуга с меткой в комментарии (';50,10 G12', ';50,15 G13')."""
    if re.search(r'\bG12\b', code) or re.search(r'\bG12\b', comment):
        return 12
    if re.search(r'\bG13\b', code) or re.search(r'\bG13\b', comment):
        return 13
    return None


def nc_explicit_leads(text, orig):
    """В кадрах входа/выхода без G-кода (модальная дуга нового постпроцессора) - явный G2/G3,
    как было в исходной программе (по N-номеру): правка контура не должна менять их модальность."""
    def modes(t):
        res, mode = {}, None
        for line in t.replace('\r\n', '\n').split('\n'):
            nnum, code, comment = _nf_split(line)
            for g in re.findall(r'\bG(\d+)\b', code):
                if int(g) in _NF_MOTION_G:
                    mode = int(g)
            if _nf_lead(code, comment) and nnum.strip():
                res[nnum.strip()] = mode
        return res
    om = modes(orig)
    crlf = '\r\n' in text
    out = []
    for line in text.replace('\r\n', '\n').split('\n'):
        nnum, code, comment = _nf_split(line)
        if nnum.strip() in om and _nf_lead(code, comment) and om[nnum.strip()] in (1, 2, 3) \
                and not re.search(r'\bG0*[0-3]\b', code):
            line = nnum + 'G%d ' % om[nnum.strip()] + code.lstrip() + comment
        out.append(line)
    return ('\r\n' if crlf else '\n').join(out)


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


def _nf_pointset(points, tol=0.001):
    """Функция-проверка: точка (x, y) ближе tol к одной из points."""
    grid = {}
    for px, py in points or ():
        grid.setdefault((round(px / tol), round(py / tol)), []).append((px, py))
    if not grid:
        return lambda x, y: False
    def has(x, y):
        if x is None:
            return False
        gx, gy = round(x / tol), round(y / tol)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for px, py in grid.get((gx + dx, gy + dy), ()):
                    if math.hypot(px - x, py - y) <= tol:
                        return True
        return False
    return has


def _nf_el_dist(e, px, py):
    """Расстояние от точки до элемента (прямая/дуга с R), None - элемент некорректен."""
    x0, y0, x1, y1 = e['x0'], e['y0'], e['x1'], e['y1']
    if e['mode'] == 1:
        dx, dy = x1 - x0, y1 - y0
        L2 = dx * dx + dy * dy
        t = 0.0 if L2 < 1e-18 else max(0.0, min(1.0, ((px - x0) * dx + (py - y0) * dy) / L2))
        return math.hypot(px - x0 - t * dx, py - y0 - t * dy)
    R = float(e['R'])
    dx, dy = x1 - x0, y1 - y0
    d = math.hypot(dx, dy)
    if d < 1e-12 or d > 2 * R + 1e-9:
        return None
    h = math.sqrt(max(R * R - d * d / 4.0, 0.0))
    sg = -1 if e['mode'] == 2 else 1
    cx = (x0 + x1) / 2 + sg * (-dy) / d * h
    cy = (y0 + y1) / 2 + sg * dx / d * h
    a0, a1, ap = math.atan2(y0 - cy, x0 - cx), math.atan2(y1 - cy, x1 - cx), math.atan2(py - cy, px - cx)
    if e['mode'] == 2:
        inside = (a0 - ap) % (2 * math.pi) <= (a0 - a1) % (2 * math.pi)
    else:
        inside = (ap - a0) % (2 * math.pi) <= (a1 - a0) % (2 * math.pi)
    if inside:
        return abs(math.hypot(px - cx, py - cy) - R)
    return min(math.hypot(px - x0, py - y0), math.hypot(px - x1, py - y1))


def _nf_el_proj(e, px, py):
    """Ближайшая к (px, py) точка элемента."""
    x0, y0, x1, y1 = e['x0'], e['y0'], e['x1'], e['y1']
    if e['mode'] == 1:
        dx, dy = x1 - x0, y1 - y0
        L2 = dx * dx + dy * dy
        t = 0.0 if L2 < 1e-18 else max(0.0, min(1.0, ((px - x0) * dx + (py - y0) * dy) / L2))
        return x0 + t * dx, y0 + t * dy
    R = float(e['R'])
    dx, dy = x1 - x0, y1 - y0
    d = math.hypot(dx, dy)
    h = math.sqrt(max(R * R - d * d / 4.0, 0.0))
    sg = -1 if e['mode'] == 2 else 1
    cx = (x0 + x1) / 2 + sg * (-dy) / d * h
    cy = (y0 + y1) / 2 + sg * dx / d * h
    r = math.hypot(px - cx, py - cy)
    if r < 1e-12:
        return x0, y0
    qx, qy = cx + (px - cx) / r * R, cy + (py - cy) / r * R
    if abs(_nf_el_dist(e, qx, qy) or 1) < 1e-9:
        return qx, qy
    return min(((x0, y0), (x1, y1)), key=lambda q: math.hypot(q[0] - px, q[1] - py))


def nc_contours(text):
    """Контуры программы: {№: {'start': (x, y) конец G12, 'els': [кадры], 'ok': только G1/G2/G3}}.
    Кадр: {'i': строка, 'x0','y0','x1','y1', 'mode', 'R' (строка или None), 'Xs','Ys' (строки)}."""
    lines = text.replace('\r\n', '\n').split('\n')
    res = {}
    mode, x, y = None, None, None
    ct_n, cur = 0, None
    for i, line in enumerate(lines):
        nnum, code, comment = _nf_split(line)
        toks = code.split()
        if not toks:
            continue
        parsed = all(_NF_TOKEN_OK.match(t) for t in toks)
        if not parsed:
            if cur is not None and re.search(r'(?<![A-Z\[.])[XY]-?\d', code):
                cur['ok'] = False
            continue
        gl = [float(t[1:]) for t in toks if t[0] == 'G']
        for g in gl:
            if g == int(g) and int(g) in _NF_MOTION_G:
                mode = int(g)
        words = dict(_NF_WORD.findall(' '.join(toks)))
        if 'X' not in words and 'Y' not in words:
            continue
        nx = float(words['X']) if 'X' in words else x
        ny = float(words['Y']) if 'Y' in words else y
        lead = _nf_lead(code, comment)
        if lead == 12:
            ct_n += 1
            cur = res[ct_n] = {'start': (nx, ny), 'els': [], 'ok': True, 'g12': i}
        elif lead == 13 or 40.0 in gl:
            cur = None
        elif cur is not None:
            if mode not in (1, 2, 3) or re.search(r'[A-Z]{2,}\(', code) or \
                    not all(g in (1, 2, 3) for g in gl) or (mode in (2, 3) and 'R' not in words):
                cur['ok'] = False
            cur['els'].append({'i': i, 'x0': x, 'y0': y, 'x1': nx, 'y1': ny, 'mode': mode,
                               'R': words.get('R') if mode in (2, 3) else None,
                               'Xs': words.get('X'), 'Ys': words.get('Y')})
        x, y = nx, ny
    return res


NF_OPEN_GAP = 0.05   # разрыв контура больше 50 мкм - намеренный (доработка другим инструментом), не соединять


def _nf_contour_sig(c):
    """(ориентация, bbox, точки) контура для поиска пар. Незамкнутый контур (разрыв линии,
    который дорабатывается другим инструментом) в пары не входит - None."""
    pts = [(e['x1'], e['y1']) for e in c['els']]
    if len(pts) < 3:
        return None
    sx, sy = c['start']
    if math.hypot(pts[-1][0] - sx, pts[-1][1] - sy) > NF_OPEN_GAP:
        return None
    a = 0.0
    for (x0, y0), (x1, y1) in zip(pts, pts[1:] + pts[:1]):
        a += x0 * y1 - x1 * y0
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    return (a > 0, (min(xs), min(ys), max(xs), max(ys)), pts)


def nc_find_pairs(conts, tol=0.001):
    """conts: {(файл, №контура): контур}. Пары прямой/обратный проход одной геометрии:
    противоположное направление, тот же габарит (±2 мкм), совпадают >= 80% вершин
    (CAM аппроксимирует дугами каждое направление отдельно - часть вершин расходится)."""
    sigs = {k: _nf_contour_sig(c) for k, c in conts.items() if c['ok']}
    sigs = {k: v for k, v in sigs.items() if v}
    keys = sorted(sigs)
    used, pairs = set(), []
    for ia, ka in enumerate(keys):
        if ka in used:
            continue
        oa, ba, pa = sigs[ka]
        for kb in keys[ia + 1:]:
            if kb in used:
                continue
            ob, bb, pb = sigs[kb]
            if oa == ob or max(abs(u - v) for u, v in zip(ba, bb)) > 0.002:
                continue
            small, big = (pa, pb) if len(pa) <= len(pb) else (pb, pa)
            if len(big) > 1.2 * len(small) + 2:
                continue
            has = _nf_pointset(big, tol)
            if sum(1 for p in small if has(*p)) >= 0.80 * len(small) and \
                    _nf_curve_gap(conts[ka], conts[kb]) <= 0.02:
                pairs.append((ka, kb)); used |= {ka, kb}
                break
    return pairs


def _nf_curve_gap(ca, cb):
    """Наибольшее расстояние от вершин одного контура до линии другого (в обе стороны), мм.
    У настоящей пары прямой/обратный проход - единицы мкм (аппроксимация CAM)."""
    def one(pa, cb):
        G, h = {}, 0.5
        for e in cb['els']:
            m = min(abs(float(e['R'])), 2.0) if e['mode'] in (2, 3) and e.get('R') else 0.0
            for gx in range(int(math.floor((min(e['x0'], e['x1']) - m) / h)) - 1,
                            int(math.floor((max(e['x0'], e['x1']) + m) / h)) + 2):
                for gy in range(int(math.floor((min(e['y0'], e['y1']) - m) / h)) - 1,
                                int(math.floor((max(e['y0'], e['y1']) + m) / h)) + 2):
                    G.setdefault((gx, gy), []).append(e)
        w = 0.0
        for e in pa['els']:
            px, py = e['x1'], e['y1']
            ds = [d for d in (_nf_el_dist(q, px, py) for q in G.get((int(math.floor(px / h)), int(math.floor(py / h))), ()))
                  if d is not None]
            w = max(w, min(ds) if ds else 1e9)
            if w > 1.0:
                break
        return w
    return max(one(ca, cb), one(cb, ca))


def _nf_rebuild_one(part, canon, tol=0.001):
    """Контур part (обратный проход) как точное обращение контура canon (уже исправленного).
    Возвращает ((новые коды по строкам, вставки перед строками, удаляемые строки), None) или (None, причина)."""
    if not part or not part['ok'] or not part['els']:
        return None, 'обратный проход не разобран'
    # обращение канонического контура
    rev = []
    for e in reversed(canon['els']):
        m = e['mode'] if e['mode'] == 1 else (3 if e['mode'] == 2 else 2)
        rev.append({'x0': e['x1'], 'y0': e['y1'], 'x1': e['x0'], 'y1': e['y0'], 'mode': m, 'R': e['R']})
    sx, sy = part['start']
    g12_new = None
    best = min(((_nf_el_dist(e, sx, sy), k) for k, e in enumerate(rev) if _nf_el_dist(e, sx, sy) is not None),
               default=None)
    if best is not None and tol < best[0] <= 0.02:
        # точка входа обратного прохода (G12) лежит рядом с общей геометрией, но не на ней (CAM) -
        # переносим её на геометрию прямого прохода
        sx, sy = _nf_el_proj(rev[best[1]], sx, sy)
        g12_new = (sx, sy)
    k0 = next((k for k, e in enumerate(rev) if math.hypot(e['x0'] - sx, e['y0'] - sy) <= tol), None)
    if k0 is None:
        # рядом (< NF_MIN_LEN) есть вершина - сдвинуть её в точку старта, чтобы не родился микро-кадр
        near = min(range(len(rev)), key=lambda k: math.hypot(rev[k]['x0'] - sx, rev[k]['y0'] - sy))
        if math.hypot(rev[near]['x0'] - sx, rev[near]['y0'] - sy) < NF_MIN_LEN:
            vx, vy = rev[near]['x0'], rev[near]['y0']
            a_new = dict(rev[near - 1], x1=sx, y1=sy)
            b_new = dict(rev[near], x0=sx, y0=sy)
            def ok(v):
                return v is not None and v <= 5e-4
            # S на следующем элементе -> старая вершина должна лечь на продлённый предыдущий, и наоборот
            if (ok(_nf_el_dist(rev[near], sx, sy)) and ok(_nf_el_dist(a_new, vx, vy))) or \
                    (ok(_nf_el_dist(rev[near - 1], sx, sy)) and ok(_nf_el_dist(b_new, vx, vy))):
                rev[near], rev[near - 1] = b_new, a_new
                k0 = near
    if k0 is None:
        # точки старта нет среди вершин - разрезать ближайший элемент в точке старта
        best = None
        for k, e in enumerate(rev):
            d = _nf_el_dist(e, sx, sy)
            if d is not None and (best is None or d < best[0]):
                best = (d, k)
        if best is None or best[0] > 0.02:
            return None, 'начало обратного прохода не найдено в исправленном контуре'
        k = best[1]
        e = rev[k]
        rev[k:k + 1] = [dict(e, x1=sx, y1=sy), dict(e, x0=sx, y0=sy)]
        k0 = k + 1
    rev = rev[k0:] + rev[:k0]
    P = part['els']
    has_p = _nf_pointset([(pe['x1'], pe['y1']) for pe in P] + [part['start']], tol)

    def center(e):
        R = float(e['R'])
        dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
        d = math.hypot(dx, dy)
        if d < 1e-12 or d > 2 * R:
            return None
        h = math.sqrt(max(R * R - d * d / 4.0, 0.0))
        sg = -1 if e['mode'] == 2 else 1
        return ((e['x0'] + e['x1']) / 2 + sg * (-dy) / d * h, (e['y0'] + e['y1']) / 2 + sg * dx / d * h)

    def try_join(a, b):
        """Склейка двух соседних элементов в один (одна прямая или одна дуга), иначе None."""
        if a['mode'] != b['mode']:
            return None
        if a['mode'] == 1:
            dx, dy = b['x1'] - a['x0'], b['y1'] - a['y0']
            L = math.hypot(dx, dy)
            if L < 1e-12 or abs((a['x1'] - a['x0']) * dy - (a['y1'] - a['y0']) * dx) / L > 1e-4:
                return None
            return dict(a, x1=b['x1'], y1=b['y1'])
        if abs(float(a['R']) - float(b['R'])) > 1e-6:
            return None
        ca, cb = center(a), center(b)
        if ca is None or cb is None:
            return None
        R = float(a['R'])
        m = dict(a, x1=b['x1'], y1=b['y1'])
        # обе части должны лежать на одной дуге: стык и середины частей - не дальше 0.1 мкм от общей дуги
        chk = [(a['x1'], a['y1'])]
        for e, c in ((a, ca), (b, cb)):
            a0 = math.atan2(e['y0'] - c[1], e['x0'] - c[0])
            a1 = math.atan2(e['y1'] - c[1], e['x1'] - c[0])
            dd = (a1 - a0 + math.pi) % (2 * math.pi) - math.pi
            chk.append((c[0] + R * math.cos(a0 + dd / 2), c[1] + R * math.sin(a0 + dd / 2)))
        for px, py in chk:
            dv = _nf_el_dist(m, px, py)
            if dv is None or dv > 1e-4:
                return None
        # суммарный угол должен остаться < 180° (R без знака)
        def ang(px, py, c):
            return math.atan2(py - c[1], px - c[0])
        sw = 0.0
        for e, c in ((a, ca), (b, cb)):
            d = ang(e['x1'], e['y1'], c) - ang(e['x0'], e['y0'], c)
            d = (d + math.pi) % (2 * math.pi) - math.pi
            sw += abs(d)
        if sw >= math.pi - 1e-6 or math.hypot(b['x1'] - a['x0'], b['y1'] - a['y0']) > 2 * R:
            return None
        return dict(a, x1=b['x1'], y1=b['y1'])

    # вершины, которых нет у обратного прохода (его собственные точки разбиения другие) - склеить
    merged = [rev[0]]
    for e in rev[1:]:
        last = merged[-1]
        if not has_p(last['x1'], last['y1']):
            jn = try_join(last, e)
            if jn is not None:
                merged[-1] = jn
                continue
        merged.append(e)
    rev = merged

    has_rev = _nf_pointset([(e['x1'], e['y1']) for e in rev], tol)
    j, new, ins = 0, {}, {}
    pending = []
    for m, e in enumerate(rev):
        if m == len(rev) - 1:
            idx = len(P) - 1
            if idx < j:
                return None, 'кадры обратного прохода не сопоставились'
        else:
            idx = None
            if has_p(e['x1'], e['y1']):
                idx = next((q for q in range(j, len(P) - 1)
                            if math.hypot(P[q]['x1'] - e['x1'], P[q]['y1'] - e['y1']) <= tol), None)
            if idx is None:
                code = 'G%d X%s Y%s' % (e['mode'], _nf_fmt(e['x1']), _nf_fmt(e['y1']))
                if e['mode'] in (2, 3):
                    code += ' R%s' % e['R']
                if j < len(P) - 1 and not has_rev(P[j]['x1'], P[j]['y1']):
                    # свободный кадр обратного прохода (его вершины нет в общей геометрии) - занять его
                    new[P[j]['i']] = code
                    if pending:
                        ins[P[j]['i']] = pending
                        pending = []
                    j += 1
                else:
                    # свободного кадра нет - вставить отдельный кадр перед следующим
                    pending.append(code + ' ;fix')
                continue
        pe = P[idx]
        if m == len(rev) - 1:
            gx, gy = g12_new if g12_new is not None else part['start']
            code = 'G%d X%s Y%s' % (e['mode'], _nf_fmt(gx), _nf_fmt(gy))
        else:
            code = 'G%d X%s Y%s' % (e['mode'], pe['Xs'] or _nf_fmt(pe['x1']), pe['Ys'] or _nf_fmt(pe['y1']))
        if e['mode'] in (2, 3):
            code += ' R%s' % e['R']
        new[pe['i']] = code
        if pending:
            ins[pe['i']] = pending
            pending = []
        j = idx + 1
    dele = set(pe['i'] for pe in P if pe['i'] not in new)
    if g12_new is not None:
        new[('g12', part['g12'])] = g12_new
    return (new, ins, dele), None


def nc_rebuild_reverse(text, jobs, tol=0.001):
    """Обратные проходы в text строятся по исправленным прямым: jobs = {№ контура: контур-образец}.
    Файл разбирается один раз. Возвращает (новый текст или None, {№: причина отказа})."""
    crlf = '\r\n' in text
    lines = text.replace('\r\n', '\n').split('\n')
    conts = nc_contours(text)
    new, ins, dele, errs = {}, {}, set(), {}
    for ct, canon in jobs.items():
        if canon is None:
            errs[ct] = 'нет исправленного прямого прохода'
            continue
        r, why = _nf_rebuild_one(conts.get(ct), canon, tol)
        if r is None:
            errs[ct] = why
            continue
        new.update(r[0]); ins.update(r[1]); dele |= r[2]
    if not new and not dele:
        return None, errs
    out = []
    for i, l in enumerate(lines):
        if i in ins:
            out.extend(ins[i])
        if i in dele:
            continue
        if i in new:
            nnum, _code, comment = _nf_split(l)
            l = nnum + new[i] + ' ' + comment
        elif ('g12', i) in new:            # перенос точки входа G12 на общую геометрию
            gx, gy = new[('g12', i)]
            nnum, code, comment = _nf_split(l)
            code = re.sub(r'X-?\d*\.?\d+', 'X' + _nf_fmt(gx), code, count=1)
            code = re.sub(r'Y-?\d*\.?\d+', 'Y' + _nf_fmt(gy), code, count=1)
            l = nnum + code + comment
        out.append(l)
    return ('\r\n' if crlf else '\n').join(out), errs


def _nf_el_tan(e, at_end):
    """Направление движения элемента (рад) в начале/конце."""
    if e['mode'] == 1:
        return math.atan2(e['y1'] - e['y0'], e['x1'] - e['x0'])
    R = float(e['R'])
    dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
    d = math.hypot(dx, dy)
    if d < 1e-12 or d > 2 * R + 1e-9:
        return math.atan2(dy, dx)
    h = math.sqrt(max(R * R - d * d / 4.0, 0.0))
    sg = -1 if e['mode'] == 2 else 1
    cx = (e['x0'] + e['x1']) / 2 + sg * (-dy) / d * h
    cy = (e['y0'] + e['y1']) / 2 + sg * dx / d * h
    px, py = (e['x1'], e['y1']) if at_end else (e['x0'], e['y0'])
    a = math.atan2(py - cy, px - cx)
    return a - math.pi / 2 if e['mode'] == 2 else a + math.pi / 2


def _nf_join(a, b):
    """Склейка двух соседних элементов в один (прямая или одна дуга), иначе None."""
    if a['mode'] != b['mode']:
        return None
    m = dict(a, x1=b['x1'], y1=b['y1'])
    if a['mode'] == 1:
        dv = _nf_el_dist(m, a['x1'], a['y1'])
        return m if dv is not None and dv <= 1e-4 else None
    if abs(float(a['R']) - float(b['R'])) > 1e-6:
        return None
    if math.hypot(b['x1'] - a['x0'], b['y1'] - a['y0']) > 2 * float(a['R']):
        return None
    # стык и середины частей - на общей дуге (0.1 мкм); суммарный угол < 180°
    if (_nf_el_dist(m, a['x1'], a['y1']) or 1) > 1e-4:
        return None
    for e in (a, b):
        mx, my = (e['x0'] + e['x1']) / 2, (e['y0'] + e['y1']) / 2
        if (_nf_el_dist(m, mx, my) or 0) > 0.05:      # грубая проверка, что дуга не "перевернулась"
            return None
    ta, tb = _nf_el_tan(m, False), _nf_el_tan(m, True)
    sw = (ta - tb) % (2 * math.pi) if a['mode'] == 2 else (tb - ta) % (2 * math.pi)
    if sw >= math.pi - 1e-6:
        return None
    return m


def nc_move_entries(text, min_line=2.0, targets=None):
    """Перенос входа/выхода контура из дуги на середину самой длинной прямой контура.
    Подвод (G0, G42, G12) и отвод (G13, G40) переносятся как жёсткое целое: то же положение
    относительно касательной контура. Резание (траектория) не меняется; разрезанная в старой
    точке входа дуга склеивается. targets = {№ контура: (x, y)} - перенести именно в эту точку
    (обратный проход - в точку прямого). Возвращает (новый текст или None, лог, число перенесённых)."""
    crlf = '\r\n' in text
    lines = text.replace('\r\n', '\n').split('\n')
    conts = nc_contours(text)
    log, moved = [], 0
    no_line, no_room, joint_moved = [], [], []
    edits, dele, ins = {}, set(), {}

    def xy_of(i):
        _n, code, _c = _nf_split(lines[i])
        mx = re.search(r'X(-?\d*\.?\d+)', code); my = re.search(r'Y(-?\d*\.?\d+)', code)
        return (float(mx.group(1)), float(my.group(1))) if mx and my else None

    def set_xy(i, x, y):
        nnum, code, comment = _nf_split(lines[i] if i not in edits else edits[i])
        code = re.sub(r'X-?\d*\.?\d+', 'X' + _nf_fmt(x), code, count=1)
        code = re.sub(r'Y-?\d*\.?\d+', 'Y' + _nf_fmt(y), code, count=1)
        edits[i] = nnum + code + comment

    for ct, c in conts.items():
        E = c['els']
        if not c['ok'] or len(E) < 3:
            continue
        if targets is not None and ct not in targets:
            continue
        g12 = c['g12']
        sx, sy = c['start']
        first, last = E[0], E[-1]
        if math.hypot(last['x1'] - sx, last['y1'] - sy) > 1e-3:
            continue                                   # контур не замкнут - не трогаем
        # вход уже на прямой (первый и последний - соосные прямые)?
        if targets is None and first['mode'] == 1 and last['mode'] == 1 and \
                abs((_nf_el_tan(first, False) - _nf_el_tan(last, True) + math.pi) % (2 * math.pi) - math.pi) < 1e-4:
            continue
        # строки подвода/отвода
        i42 = g12 - 1
        if 'G42' not in lines[i42] and 'G41' not in lines[i42]:
            continue
        i0 = next((q for q in range(i42 - 1, max(i42 - 6, 0), -1)
                   if re.search(r'\bG0\b', _nf_split(lines[q])[1]) and xy_of(q)), None)
        i13 = last['i'] + 1
        if _nf_lead(*_nf_split(lines[i13])[1:]) != 13 or 'G40' not in lines[i13 + 1]:
            continue
        i40 = i13 + 1
        p40 = xy_of(i40)
        i40s = [i40]
        for q in range(i40 + 1, min(i40 + 40, len(lines))):
            if 'PREPART' in lines[q] or 'G12' in lines[q]:
                break
            if 'G40' in lines[q] and xy_of(q) is not None and \
                    math.hypot(xy_of(q)[0] - p40[0], xy_of(q)[1] - p40[1]) < 1e-9:
                i40s.append(q)
        # склейка разрезанного элемента в старой точке входа
        C = list(E)
        J = _nf_join(dict(last), dict(first))
        if J is not None:
            C = [J] + C[1:-1]
        # ближайшая к старому входу достаточно длинная прямая, если идти ПРОТИВ ЧАСОВОЙ стрелки
        # (по геометрии, а не по ходу прохода - прямой и обратный проходы выбирают одну прямую)
        lead = math.hypot(xy_of(i42)[0] - sx, xy_of(i42)[1] - sy)
        need = max(min_line, 4 * lead)
        area = 0.0
        for e in E:
            area += e['x0'] * e['y1'] - e['x1'] * e['y0']
        n = len(C)
        if J is not None:              # C[0] содержит старый вход
            order = list(range(n)) if area > 0 else [0] + list(range(n - 1, 0, -1))
        else:                          # старый вход - вершина между C[-1] и C[0]
            order = list(range(n)) if area > 0 else list(range(n - 1, -1, -1))
        best = None
        for k in order:
            e = C[k]
            if e['mode'] == 1 and math.hypot(e['x1'] - e['x0'], e['y1'] - e['y0']) >= need:
                best = (math.hypot(e['x1'] - e['x0'], e['y1'] - e['y0']), k)
                break
        def elen(e):
            return math.hypot(e['x1'] - e['x0'], e['y1'] - e['y0'])
        if targets is not None:
            # принудительно в заданную точку: вершина или разрез элемента в этой точке
            tx, ty = targets[ct]
            kv = next((k for k, e in enumerate(C) if math.hypot(e['x0'] - tx, e['y0'] - ty) <= 1e-3), None)
            if kv is not None:
                newC = C[kv:] + C[:kv]
                newC[0] = dict(newC[0], x0=tx, y0=ty)
                newC[-1] = dict(newC[-1], x1=tx, y1=ty)
            else:
                ke = min(range(len(C)), key=lambda k: _nf_el_dist(C[k], tx, ty) if _nf_el_dist(C[k], tx, ty) is not None else 1e9)
                if (_nf_el_dist(C[ke], tx, ty) or 1) > 1e-3:
                    no_room.append(ct)
                    continue
                e = C[ke]
                newC = [dict(e, x0=tx, y0=ty)] + C[ke + 1:] + C[:ke] + [dict(e, x1=tx, y1=ty)]
            mx_, my_ = tx, ty
            a_new = _nf_el_tan(newC[0], False)
            joint_moved.append(ct)
        elif best is not None:
            k = best[1]
            Lk = C[k]
            mx_, my_ = (Lk['x0'] + Lk['x1']) / 2, (Lk['y0'] + Lk['y1']) / 2
            newC = [dict(Lk, x0=mx_, y0=my_)] + C[k + 1:] + C[:k] + [dict(Lk, x1=mx_, y1=my_)]
            a_new = _nf_el_tan(Lk, False)
        else:
            # кривой контур без прямых: переносим, только если у входа микро-кусок разрезанной дуги -
            # на ближайший против часовой стрелки стык двух нормальных элементов без излома
            if min(elen(first), elen(last)) >= NF_MIN_LEN or len(C) < 3:
                no_line.append(ct)
                continue
            n = len(C)
            vorder = list(range(1, n)) if area > 0 else list(range(n - 1, 0, -1))
            kv = None
            for k in vorder:
                ea, eb = C[k - 1], C[k]
                if elen(ea) < NF_MIN_LEN or elen(eb) < NF_MIN_LEN:
                    continue
                kink = abs((_nf_el_tan(eb, False) - _nf_el_tan(ea, True) + math.pi) % (2 * math.pi) - math.pi)
                if kink < math.radians(0.1):
                    kv = k
                    break
            if kv is None:
                no_line.append(ct)
                continue
            newC = C[kv:] + C[:kv]
            mx_, my_ = newC[0]['x0'], newC[0]['y0']
            a_new = _nf_el_tan(newC[0], False)
            joint_moved.append(ct)
        # поворот подвода/отвода: старая касательная в S -> направление контура в новой точке
        # направление контура в старом входе - по первому не-микро элементу (у микро-кадра оно случайное)
        f_ok = next((e for e in E if math.hypot(e['x1'] - e['x0'], e['y1'] - e['y0']) >= NF_MIN_LEN), first)
        th = a_new - _nf_el_tan(f_ok, False)
        co, si = math.cos(th), math.sin(th)

        def tr(p):
            dx, dy = p[0] - sx, p[1] - sy
            return (mx_ + co * dx - si * dy, my_ + si * dx + co * dy)
        # проверка зазора: точки подвода/отвода не ближе к контуру, чем были
        def clear(p, elems):
            return min((_nf_el_dist(e, p[0], p[1]) or 0) for e in elems)
        pts_old = [xy_of(i42), xy_of(i13), p40] + ([xy_of(i0)] if i0 is not None else [])
        # точки подвода/отвода: на стороне инструмента от прямой и не ближе своего вылета к остальному контуру
        side = 1 if 'G42' in lines[i42] else -1
        nrx, nry = math.sin(a_new) * side, -math.cos(a_new) * side   # нормаль в сторону инструмента
        others = newC[1:-1]
        ok = True
        is_joint = bool(joint_moved) and joint_moved[-1] == ct
        for p in pts_old:
            q = tr(p)
            if is_joint:
                # перенос на соседний стык (микроны): подвод должен остаться так же далеко от контура
                if clear(q, newC) < 0.9 * clear(p, E) - 1e-3:
                    ok = False
            elif (q[0] - mx_) * nrx + (q[1] - my_) * nry <= 0:
                ok = False
            elif others and clear(q, others) < 0.8 * math.hypot(p[0] - sx, p[1] - sy):
                ok = False
        if not ok:
            no_room.append(ct)
            if joint_moved and joint_moved[-1] == ct:
                joint_moved.pop()
            continue
        # строки контура: новые элементы в те же строки (N-номера сохраняются)
        slots = [e['i'] for e in E]
        codes = []
        for e in newC:
            code = 'G%d X%s Y%s' % (e['mode'], _nf_fmt(e['x1']), _nf_fmt(e['y1']))
            if e['mode'] in (2, 3):
                code += ' R%s' % e['R']
            codes.append(code)
        for q, i in enumerate(slots):
            nnum, _c, comment = _nf_split(lines[i])
            if q < len(codes):
                edits[i] = nnum + codes[q] + ' ' + comment
            else:
                dele.add(i)
        if len(codes) > len(slots):
            ins[slots[-1]] = [cd + ' ;fix' for cd in codes[len(slots):]]
        set_xy(g12, mx_, my_)
        set_xy(i42, *tr(xy_of(i42)))
        set_xy(i13, *tr(xy_of(i13)))
        for q in i40s:
            set_xy(q, *tr(p40))
        if i0 is not None:
            set_xy(i0, *tr(xy_of(i0)))
        moved += 1
    def lst(v):
        return ', '.join(map(str, v[:6])) + ('…' if len(v) > 6 else '')
    if no_line:
        log.append('  вход в дуге, но нет длинной прямой - вход оставлен: контуров %d (№ %s)' % (len(no_line), lst(no_line)))
    if no_room:
        log.append('  ! вход в дуге, на новом месте мало места для подвода - вход оставлен: контуров %d (№ %s)'
                   % (len(no_room), lst(no_room)))
    if not moved:
        return None, log, 0
    out = []
    for i, l in enumerate(lines):
        if i in dele:
            continue
        out.append(edits.get(i, l))
        out.extend(ins.get(i, ()))
    log.insert(0, '  вход/выход перенесён из дуги на середину прямой: контуров %d' % (moved - len(joint_moved)))
    if joint_moved:
        log.insert(1, '  вход/выход кривых контуров перенесён с микро-куска на соседний стык элементов: %d'
                   % len(joint_moved))
    return ('\r\n' if crlf else '\n').join(out), log, moved


def nc_update_dla(text):
    """Пересчитать CLN(DLAn) у каждого контура после правок.
    CAM ставит для контура DLA = (кадров между G12 и G13) - 2, но не больше общего CLN(DLA..) в шапке.
    Если Fix уменьшил число кадров, а DLA остался старым, окно контроля столкновений (CollErr0)
    захватывает замыкание контура и ЧПУ без ошибки выбрасывает весь контур - он не фрезеруется."""
    nl = '\r\n' if '\r\n' in text else '\n'
    L = text.split(nl)
    cap = None
    for l in L:
        if re.search(r'\.COL\d+', l.split(';')[0]):
            break
        m = re.search(r'CLN\(DLA(\d+)\)', l)
        if m:
            cap = int(m.group(1))
    if cap is None:
        return text, 0
    counts, cur, n, inc = {}, None, 0, False
    for l in L:
        c = l.split(';')[0]
        m = re.search(r'\.COL(\d+)\b', c)
        if m:
            cur, n, inc = m.group(1), 0, False
            continue
        if cur is None:
            continue
        # маркер G12/G13 ищем во всей строке: новый постпроцессор пишет дугу
        # входа/выхода настоящей G2/G3, а G12/G13 оставляет в комментарии
        # (`G2 X.. Y.. R1.3 ;50,10 G12`) - иначе границ контура не видно (V8.8)
        if re.search(r'\bG12\b', l):
            inc, n = True, 0
            continue
        if re.search(r'\bG13\b', l):
            if inc:
                counts[cur] = n
            inc = False
            continue
        if inc and re.search(r'[XY]-?\d', c):
            n += 1
    changed, part = 0, None
    for i, l in enumerate(L):
        c = l.split(';')[0]
        m = re.search(r'\.PART(\d+)\b', c)
        if m:
            part = m.group(1)
            continue
        m = re.search(r'CLN\(DLA(\d+)\)', c)
        if m and part is not None:
            if part in counts and counts[part] >= 3:
                want = min(cap, counts[part] - 2)
                if want != int(m.group(1)):
                    L[i] = l[:m.start(1)] + str(want) + l[m.end(1):]
                    changed += 1
            part = None
    return (nl.join(L), changed) if changed else (text, 0)


def nc_is_meas_line(line):
    """Строка блока измерения щупом (постпроцессор AlphaCAM/Anderson):
    ;***** Altitude measurement and compensation MP(n) *****
    #MPX!=... : #MPY!=...
    P IHOC(PD=0)
    IF (#IHOC? = TRUE) AND (#IHOCPL? = TRUE) THEN GOTO .SHAPEn ENDIF
    Флаг #IHOCNS?=TRUE в начале цикла остаётся (он есть и в программах без измерений)."""
    return ('Altitude measurement' in line
            or re.search(r'#MP[XY]!\s*=', line) is not None
            or re.search(r'\bIHOC\s*\(', line) is not None
            or re.search(r'IF\s*\(\s*#IHOC\?\s*=\s*TRUE\s*\)', line) is not None)


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


def nc_fix_text(text, dtip=0.15, ang_max=90, safety=0.03, min_len=NF_MIN_LEN, min_radius=None, max_dev=0.0005,
                skip_ct=(), sym_ct=(), protect=(), fix_radius=True):
    """Проверка/коррекция текста NC-программы. fix_radius=False - радиусы не трогать.
    Возвращает (новый_текст или None если правок нет, список строк отчёта, (дуг, микро, откл_мм)).
    skip_ct  - номера контуров (по счёту G12), которые не трогать (обратные проходы, строятся отдельно);
    sym_ct   - контуры, у которых есть обратный проход: малые дуги увеличиваются с обеих сторон;
    protect  - точки (x, y), которые нельзя удалять (начало обратного прохода)."""
    log = []
    _prot = _nf_pointset(protect)
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
            log.append('  инфо: эквидистанта Ø%.4f, резец %g° (Ø%.4f на гл. %.3f), эквидистанта соответствует ~%.1f°'
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
    ct_n, ct_cur = 0, None
    ct_start = {}
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
        ct = ct_cur
        lead = _nf_lead(code, comment)
        if lead == 12:                 # вход на контур: следующие кадры - контур № ct_n
            ct_n += 1
            ct_cur, ct = ct_n, None
            ct_start[ct_n] = (nx, ny)
        elif lead == 13 or comp == 40:
            ct_cur, ct = None, None
        blocks.append({'i': i, 'code': code, 'g': gl, 'w': words, 'mode': mode, 'lead': lead,
                       'comp': comp, 'x0': x, 'y0': y, 'x1': nx, 'y1': ny, 'ct': ct})
        x, y = nx, ny

    # незамкнутые контуры (разрыв линии под другой инструмент): конец не двигать и не соединять
    _open_ends = []
    for ctn, (sx0, sy0) in ct_start.items():
        lb = [b for b in blocks if b['ct'] == ctn]
        if lb and math.hypot(lb[-1]['x1'] - sx0, lb[-1]['y1'] - sy0) > NF_OPEN_GAP:
            _open_ends.append((lb[-1]['x1'], lb[-1]['y1']))
    if _open_ends:
        _prot = _nf_pointset(list(protect) + _open_ends)
        log.append('  незамкнутых контуров (разрыв линии): %d - разрыв оставлен как есть' % len(_open_ends))

    def plain(b):
        return (not b.get('lead') and 'I' not in b['w'] and 'J' not in b['w'] and b['ct'] not in skip_ct and b['mode'] in (1, 2, 3) and b['comp'] in (41, 42)
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

    # первый и последний элементы контура (у точки входа G12) не меняются: при почти соосном
    # замыкании любое изменение направления стойка может принять за петлю и пропустить контур
    edge = set()
    _first, _last = {}, {}
    for b in blocks:
        if b['ct'] is not None:
            _first.setdefault(b['ct'], b['i'])
            _last[b['ct']] = b['i']
    edge = set(_first.values()) | set(_last.values())
    EDGE_R = 0.05      # мм: кадры с концом ближе 50 мкм к точке входа тоже не сливаются в прямые
    for b in blocks:
        st = ct_start.get(b['ct'])
        if st is not None and b['x0'] is not None and \
                (math.hypot(b['x0'] - st[0], b['y0'] - st[1]) < EDGE_R or math.hypot(b['x1'] - st[0], b['y1'] - st[1]) < EDGE_R):
            edge.add(b['i'])

    # --- «шумные» прямые участки: цепочка коротких/почти плоских дуг и отрезков, лежащая
    #     на прямой в пределах max_dev, заменяется одним G1 (стойка: Cornering error 10219 'Split') ---
    def arc_mid(b):
        x0, y0, x1, y1 = b['x0'], b['y0'], b['x1'], b['y1']
        R = float(b['w']['R'])
        dx, dy = x1 - x0, y1 - y0
        d = math.hypot(dx, dy)
        if R <= 0 or d < 1e-12 or d > 2 * R:
            return None
        sag = R - math.sqrt(R * R - d * d / 4.0)
        sgn = 1 if b['mode'] == 2 else -1          # G2: выпуклость влево от хорды, G3 - вправо
        return ((x0 + x1) / 2 + sgn * (-dy) / d * sag, (y0 + y1) / 2 + sgn * dx / d * sag)

    def seg_dist(px, py, ax, ay, bx, by):
        dx, dy = bx - ax, by - ay
        L2 = dx * dx + dy * dy
        if L2 < 1e-14:
            return math.hypot(px - ax, py - ay)
        t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / L2))
        return math.hypot(px - (ax + t * dx), py - (ay + t * dy))

    SHORT = 0.05   # мм: цепочка заменяется, только если в ней есть дуга или кадр короче 50 мкм
    WIG_DEV, WIG_SHORT, WIG_KINK, WIG_LEN = 0.02, 0.02, math.radians(0.5), 1.0
    r_bad = rc + safety
    n_wig = 0
    KINK = math.radians(0.3)   # на концах прямой направление не должно ломаться больше чем на 0.3°

    def blk_tan(b, at_end):
        if b['mode'] == 1:
            return math.atan2(b['y1'] - b['y0'], b['x1'] - b['x0'])
        R = float(b['w']['R'])
        dx, dy = b['x1'] - b['x0'], b['y1'] - b['y0']
        d = math.hypot(dx, dy)
        if d < 1e-12 or d > 2 * R:
            return math.atan2(dy, dx)
        hh = math.sqrt(max(R * R - d * d / 4.0, 0.0))
        sg = -1 if b['mode'] == 2 else 1
        cx = (b['x0'] + b['x1']) / 2 + sg * (-dy) / d * hh
        cy = (b['y0'] + b['y1']) / 2 + sg * dx / d * hh
        px, py = (b['x1'], b['y1']) if at_end else (b['x0'], b['y0'])
        a = math.atan2(py - cy, px - cx)
        return a - math.pi / 2 if b['mode'] == 2 else a + math.pi / 2

    def ang_diff(a, b):
        return abs((a - b + math.pi) % (2 * math.pi) - math.pi)
    n_straight = n_str_blk = 0
    dev_str = dev_mic = dev_wig = 0.0
    bad_micro = []     # строки микро-кадров, которые нельзя убрать
    k = 0
    while k < len(blocks):
        b = blocks[k]
        if not (plain(b) and b['x0'] is not None) or (b['mode'] in (2, 3) and 'R' not in b['w']) \
                or b['i'] in edge:
            k += 1
            continue
        pts = [(b['x1'], b['y1'])]
        if b['mode'] in (2, 3):
            m = arc_mid(b)
            if m is None:
                k += 1
                continue
            pts.append(m)
        best, best_dev = k, 0.0
        # "плохой" участок (микро-перегиб): кадр < 20 мкм, дуга R < эквидистанты + страховка,
        # излом > 0.5°. Его можно спрямлять с отклонением до WIG_DEV (иначе - max_dev)
        has_bad = b['mode'] in (2, 3) and 0 < float(b['w']['R']) < r_bad \
            or math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0']) < WIG_SHORT
        j = k + 1
        while j < len(blocks):
            c = blocks[j]
            if not plain(c) or c['x0'] is None or c['comp'] != b['comp'] or c['i'] in edge \
                    or abs(c['x0'] - blocks[j - 1]['x1']) > 1e-9 or abs(c['y0'] - blocks[j - 1]['y1']) > 1e-9 \
                    or _prot(c['x0'], c['y0']):
                break
            if c['mode'] in (2, 3):
                if 'R' not in c['w']:
                    break
                m = arc_mid(c)
                if m is None:
                    break
                pts.append(m)
            pts.append((c['x1'], c['y1']))
            ex, ey = c['x1'], c['y1']
            if c['mode'] in (2, 3) and 0 < float(c['w']['R']) < r_bad \
                    or math.hypot(c['x1'] - c['x0'], c['y1'] - c['y0']) < WIG_SHORT \
                    or ang_diff(blk_tan(blocks[j - 1], True), blk_tan(c, False)) > WIG_KINK:
                has_bad = True
            dev = max(seg_dist(px, py, b['x0'], b['y0'], ex, ey) for px, py in pts[:-1])
            if dev > WIG_DEV or (dev > max_dev and math.hypot(ex - b['x0'], ey - b['y0']) > WIG_LEN):
                break
            ch = math.atan2(ey - b['y0'], ex - b['x0'])
            if dev <= (WIG_DEV if has_bad else max_dev) and \
                    ang_diff(ch, blk_tan(b, False)) <= KINK and ang_diff(ch, blk_tan(c, True)) <= KINK:
                best, best_dev = j, dev
            j += 1
        if best > k:
            run = blocks[k:best + 1]
            if any(r['mode'] in (2, 3) or math.hypot(r['x1'] - r['x0'], r['y1'] - r['y0']) < SHORT for r in run):
                last = run[-1]
                nnum, code, comment = _nf_split(lines[b['i']])
                lines[b['i']] = nnum + 'G1 X%s Y%s' % (_nf_fmt(last['x1']), _nf_fmt(last['y1'])) + ' ' + comment
                b.update(mode=1, g=[1.0], w={'X': str(last['x1']), 'Y': str(last['y1'])},
                         x1=last['x1'], y1=last['y1'], code='G1')
                for r in run[1:]:
                    delete.add(r['i'])
                nxt = blocks[best + 1] if best + 1 < len(blocks) else None
                if nxt is not None and nxt['mode'] in (2, 3) and not any(g in _NF_MOTION_G for g in nxt['g']):
                    nnum, code, comment = _nf_split(lines[nxt['i']])
                    lines[nxt['i']] = nnum + 'G%d ' % nxt['mode'] + code.lstrip() + comment
                    nxt['g'] = nxt['g'] + [float(nxt['mode'])]
                if best_dev > max_dev:
                    n_wig += 1
                    dev_wig = max(dev_wig, best_dev)
                else:
                    n_straight += 1
                    dev_str = max(dev_str, best_dev)
                n_str_blk += len(run) - 1
                k = best + 1
                continue
        k += 1

    # --- микро-кадры: поглощаются предыдущим кадром, если его форма почти не меняется ---
    def elem_dev(b, ex, ey, pts, sx=None, sy=None):
        """Макс. отклонение точек pts от кадра b с началом (sx, sy) (по умолчанию его же) и концом (ex, ey);
        None - нельзя."""
        x0, y0 = (b['x0'], b['y0']) if sx is None else (sx, sy)
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
        if b['i'] in delete or b['comp'] not in (41, 42) or b['x0'] is None or b['mode'] not in (1, 2, 3) \
                or b['ct'] in skip_ct \
                or 'I' in b['w'] or 'J' in b['w']:   # полный круг через I/J - не микро-кадр
            continue
        L = math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
        if L >= min_len:
            continue
        if not plain(b):
            bad_micro.append(b['i'] + 1)
            continue
        # предыдущий оставшийся кадр того же контура
        q = k - 1
        while q >= 0 and blocks[q]['i'] in delete:
            q -= 1
        prv = blocks[q] if q >= 0 else None
        dev = None
        # кадр короче 1 мкм: оба его конца - практически одна точка, защищённая вершина
        # (точка входа обратного прохода) остаётся, какой бы конец ни ушёл
        tiny = L < 0.001

        def free(px, py, ox, oy):
            return not _prot(px, py) or (tiny and _prot(ox, oy))
        if prv is not None and plain(prv) and free(b['x0'], b['y0'], b['x1'], b['y1']):
            pts = prv.setdefault('absorbed', []) + [(prv['x1'], prv['y1'])]
            dev = elem_dev(prv, b['x1'], b['y1'], pts)
        nxt = blocks[k + 1] if k + 1 < len(blocks) else None
        forward = False
        if dev is None or dev > max_dev:
            # назад нельзя (например, сразу после входа G12) - пробуем отдать следующему кадру:
            # его начало переносится в начало микро-кадра, текст кадра не меняется
            if nxt is not None and plain(nxt) and nxt['i'] not in delete and free(b['x1'], b['y1'], b['x0'], b['y0']) \
                    and abs(nxt['x0'] - b['x1']) < 1e-9 and abs(nxt['y0'] - b['y1']) < 1e-9:
                pts_n = nxt.setdefault('absorbed', []) + [(b['x1'], b['y1'])]
                dev_n = elem_dev(nxt, nxt['x1'], nxt['y1'], pts_n, b['x0'], b['y0'])
                if dev_n is not None and dev_n <= max_dev:
                    forward, dev = True, dev_n
            if not forward:
                bad_micro.append(b['i'] + 1)
                continue
        own_g = [g for g in b['g'] if g in (1, 2, 3)]
        if own_g and nxt is not None and not any(g in _NF_MOTION_G for g in nxt['g']):
            nnum, code, comment = _nf_split(lines[nxt['i']])
            lines[nxt['i']] = nnum + 'G%d ' % own_g[-1] + code.lstrip() + comment
            nxt['g'] = nxt['g'] + [float(own_g[-1])]
        if forward:
            nxt['absorbed'] = pts_n
            nxt['x0'], nxt['y0'] = b['x0'], b['y0']
        else:
            prv['absorbed'] = pts
            set_end(prv, b['x1'], b['y1'])
        delete.add(b['i'])
        n_micro += 1
        dev_mic = max(dev_mic, dev)

    # --- внутренние скругления меньше R_min: касательная дуга R_min («шарик» радиуса R_min),
    #     без изломов; меняется только участок, куда инструмент не проходит ---
    ins_after = {}
    n_fil = 0
    dev_fil = 0.0

    def b_el(b):
        return {'x0': b['x0'], 'y0': b['y0'], 'x1': b['x1'], 'y1': b['y1'], 'mode': b['mode'],
                'R': b['w'].get('R') if b['mode'] in (2, 3) else None}

    def arc_center(e):
        R = float(e['R'])
        dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
        d = math.hypot(dx, dy)
        if d < 1e-12 or d > 2 * R + 1e-9:
            return None
        h = math.sqrt(max(R * R - d * d / 4.0, 0.0))
        sg = -1 if e['mode'] == 2 else 1
        return ((e['x0'] + e['x1']) / 2 + sg * (-dy) / d * h, (e['y0'] + e['y1']) / 2 + sg * dx / d * h, R)

    def sample(e, h):
        """Точки элемента (без начальной) с нормалью вправо от направления движения."""
        if e['mode'] == 1:
            dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
            L = math.hypot(dx, dy)
            if L < 1e-12:
                return []
            n = max(1, int(math.ceil(L / h)))
            nx, ny = dy / L, -dx / L
            return [(e['x0'] + dx * t / n, e['y0'] + dy * t / n, nx, ny) for t in range(1, n + 1)]
        c = arc_center(e)
        if c is None:
            return None
        cx, cy, R = c
        a0 = math.atan2(e['y0'] - cy, e['x0'] - cx)
        a1 = math.atan2(e['y1'] - cy, e['x1'] - cx)
        sw = a1 - a0
        if e['mode'] == 2:
            while sw > 0: sw -= 2 * math.pi
        else:
            while sw < 0: sw += 2 * math.pi
        n = max(1, int(math.ceil(abs(sw) * R / h)))
        out = []
        for t in range(1, n + 1):
            a = a0 + sw * t / n
            rx, ry = math.cos(a), math.sin(a)
            nr = (-rx, -ry) if e['mode'] == 2 else (rx, ry)      # вправо: G2 - к центру, G3 - наружу
            out.append((cx + R * rx, cy + R * ry, nr[0], nr[1]))
        return out

    def offset_of(e, side):
        """Эквидистанта элемента на rmin в сторону side (+1 вправо, -1 влево): ('L', точка, направление)
        или ('C', центр, радиус)."""
        if e['mode'] == 1:
            dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
            L = math.hypot(dx, dy)
            nx, ny = dy / L * side, -dx / L * side
            return ('L', (e['x0'] + nx * rmin, e['y0'] + ny * rmin), (dx / L, dy / L))
        cx, cy, R = arc_center(e)
        inside = (e['mode'] == 2 and side > 0) or (e['mode'] == 3 and side < 0)
        r = R - rmin if inside else R + rmin
        return ('C', (cx, cy), r) if r > 1e-9 else None

    def intersect(o1, o2):
        res = []
        if o1[0] == 'L' and o2[0] == 'L':
            (p, d), (q, f) = (o1[1], o1[2]), (o2[1], o2[2])
            den = d[0] * f[1] - d[1] * f[0]
            if abs(den) > 1e-12:
                t = ((q[0] - p[0]) * f[1] - (q[1] - p[1]) * f[0]) / den
                res.append((p[0] + d[0] * t, p[1] + d[1] * t))
            return res
        if o1[0] == 'C' and o2[0] == 'L':
            o1, o2 = o2, o1
        if o1[0] == 'L':
            (p, d), (c, r) = (o1[1], o1[2]), (o2[1], o2[2])
            fx, fy = p[0] - c[0], p[1] - c[1]
            bq = fx * d[0] + fy * d[1]
            cq = fx * fx + fy * fy - r * r
            disc = bq * bq - cq
            if disc >= 0:
                for sg in (-1, 1):
                    t = -bq + sg * math.sqrt(disc)
                    res.append((p[0] + d[0] * t, p[1] + d[1] * t))
            return res
        (c1, r1), (c2, r2) = (o1[1], o1[2]), (o2[1], o2[2])
        dx, dy = c2[0] - c1[0], c2[1] - c1[1]
        d = math.hypot(dx, dy)
        if d < 1e-12 or d > r1 + r2 or d < abs(r1 - r2):
            return res
        a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
        h = math.sqrt(max(r1 * r1 - a * a, 0.0))
        mx, my = c1[0] + a * dx / d, c1[1] + a * dy / d
        res += [(mx + h * dy / d, my - h * dx / d), (mx - h * dy / d, my + h * dx / d)]
        return res

    def foot(e, side, C):
        if e['mode'] == 1:
            dx, dy = e['x1'] - e['x0'], e['y1'] - e['y0']
            L = math.hypot(dx, dy)
            return (C[0] - dy / L * side * rmin, C[1] + dx / L * side * rmin)
        cx, cy, R = arc_center(e)
        v = math.hypot(C[0] - cx, C[1] - cy)
        return (cx + (C[0] - cx) / v * R, cy + (C[1] - cy) / v * R)

    def seg_cross(A, B):
        """Пересечения отрезков A[i]-A[i+1] и B[j]-B[j+1] (numpy): список (i, j, x, y)."""
        import numpy as np
        a0, a1 = A[:-1][:, None, :], A[1:][:, None, :]
        b0, b1 = B[:-1][None, :, :], B[1:][None, :, :]
        r = a1 - a0
        q = b1 - b0
        den = r[..., 0] * q[..., 1] - r[..., 1] * q[..., 0]
        w = b0 - a0
        with np.errstate(divide='ignore', invalid='ignore'):
            t = (w[..., 0] * q[..., 1] - w[..., 1] * q[..., 0]) / den
            u = (w[..., 0] * r[..., 1] - w[..., 1] * r[..., 0]) / den
        ok = (np.abs(den) > 1e-15) & (t >= 0) & (t <= 1) & (u >= 0) & (u <= 1)
        ii, jj = np.nonzero(ok)
        return [(int(i), int(j), float(a0[i, 0, 0] + r[i, 0, 0] * t[i, j]),
                 float(a0[i, 0, 1] + r[i, 0, 1] * t[i, j])) for i, j in zip(ii, jj)]

    try:
        import numpy as _np
    except ImportError:
        _np = None
    cts = sorted(set(b['ct'] for b in blocks if b['ct'] is not None and b['ct'] not in skip_ct))
    # контуры-круги (все элементы - дуги одной окружности, или кадр с I/J): радиусы не трогаем -
    # круг нельзя "скруглить", только испортить; если он меньше R_min - предупреждение
    circle_ct = set()
    for ctn in set(b['ct'] for b in blocks if b['ct'] is not None):
        cb = [b for b in blocks if b['ct'] == ctn and b['i'] not in delete]
        if not cb:
            continue
        if any('I' in b['w'] or 'J' in b['w'] for b in cb):
            circle_ct.add(ctn)
            continue
        if all(b['mode'] in (2, 3) and 'R' in b['w'] for b in cb):
            cs = []
            for b in cb:
                c = arc_center(b_el(b))
                cs.append(c)
            if all(c is not None for c in cs) and \
                    max(math.hypot(c[0] - cs[0][0], c[1] - cs[0][1]) for c in cs) < 0.001 and \
                    max(abs(c[2] - cs[0][2]) for c in cs) < 0.001:
                circle_ct.add(ctn)
                if cs[0][2] < rmin and fix_radius:
                    log.append('  ! круг R%.4f меньше R_min %.4f (контур %d) - не изменён, проверить в макете'
                               % (cs[0][2], rmin, ctn))
    # Контур с обратным проходом: дуги со стороны, противоположной инструменту, на обратном
    # проходе становятся внутренними. CAM их там не делает меньше эквидистанты (R = rc),
    # поэтому общая геометрия пары: с обратной стороны R >= max(R_min, эквидистанта).
    rmin_base = rmin
    r_opp = max(rmin, math.ceil(rc * 1e5 - 1e-6) / 1e5)
    n_opp = 0
    for ctn in cts if _np is not None and (fix_radius or sym_ct) else ():
        if ctn in circle_ct:
            continue
        if not fix_radius and ctn not in sym_ct:
            continue
        act = [b for b in blocks if b['ct'] == ctn and b['i'] not in delete and plain(b)]
        if not act:
            continue
        tool_side = 1 if act[0]['comp'] == 42 else -1
        sides = ((tool_side,) if fix_radius else ()) + ((-tool_side,) if ctn in sym_ct else ())
        thr = {tool_side: rmin_base, -tool_side: r_opp if fix_radius else max(rc, 0.0)}

        def small(b, side):
            if b['i'] in delete or b['mode'] not in (2, 3) or 'R' not in b['w']:
                return False
            R = float(b['w']['R'])
            sd = 1 if b['mode'] == 2 else -1
            return 0 < R < thr[side] - 1e-9 and sd == side
        k = 0
        while k < len(act):
            side = next((sd for sd in sides if small(act[k], sd)), None)
            if side is None:
                k += 1
                continue
            rmin = thr[side]
            ka = kb = k
            while kb + 1 < len(act) and small(act[kb + 1], side):
                kb += 1
            done = False
            def blen(b):
                if b['mode'] == 1 or 'R' not in b['w']:
                    return math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
                ch = math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
                R = float(b['w']['R'])
                return 2 * R * math.asin(min(1.0, ch / (2 * R))) if R > 0 else ch
            for LIM in (1.5 * rmin, 3 * rmin, 6 * rmin):
                lo, acc = ka, 0.0
                while lo > 0 and acc < LIM:
                    lo -= 1
                    acc += blen(act[lo])
                hi, acc = kb, 0.0
                while hi < len(act) - 1 and acc < LIM:
                    hi += 1
                    acc += blen(act[hi])
                win = [b for b in act[lo:hi + 1] if b['i'] not in delete]
                if not win:
                    break
                tot = sum(blen(b) for b in win)
                pts, own = [(win[0]['x0'], win[0]['y0'], 0.0, 0.0)], [0]
                h = max(min(0.003, rmin / 40.0), tot / 2000.0)
                bad = False
                for wi, b in enumerate(win):
                    sm = sample(b_el(b), h)
                    if sm is None:
                        bad = True
                        break
                    pts += sm
                    own += [wi] * len(sm)
                if bad or len(pts) < 4:
                    break
                pts[0] = (pts[0][0], pts[0][1], pts[1][2], pts[1][3])
                P = _np.array([(p[0], p[1]) for p in pts])
                O = _np.array([(p[0] + side * p[2] * rmin, p[1] + side * p[3] * rmin) for p in pts])
                # середина малого участка - точки до неё и после
                mid_w = next(wi for wi, b in enumerate(win) if b is act[ka])
                mid = own.index(mid_w)
                if mid < 2 or mid > len(O) - 3:
                    continue
                cr = seg_cross(O[:mid + 1], O[mid:])
                cr = [(i, j + mid, x, y) for i, j, x, y in cr if j + mid > i + 1]
                if not cr:
                    continue
                i, j, cx0, cy0 = max(cr, key=lambda c: c[1] - c[0])
                if i == 0 or j + 1 >= len(O) - 1:
                    continue                      # петля упирается в край окна - расширить окно
                w1, w2 = own[i + 1], own[j]
                # опорные кадры скругления - не сами малые дуги (их заменяет скругление):
                # при необходимости сдвигаются к соседям, пока касательные точки не лягут на кадры
                while w1 > 0 and small(win[w1], side):
                    w1 -= 1
                while w2 < len(win) - 1 and small(win[w2], side):
                    w2 += 1
                ok_t = False
                for _try in range(6):
                    b1, b2 = win[w1], win[w2]
                    if b1 is b2:
                        break
                    e1, e2 = b_el(b1), b_el(b2)
                    o1, o2 = offset_of(e1, side), offset_of(e2, side)
                    cands = intersect(o1, o2) if o1 and o2 else []
                    cands = [c for c in cands if math.hypot(c[0] - cx0, c[1] - cy0) < max(0.05, rmin)]
                    if not cands:
                        break
                    best = None
                    for Cc in cands:
                        Ta, Tb = foot(e1, side, Cc), foot(e2, side, Cc)
                        da, db = _nf_el_dist(e1, *Ta), _nf_el_dist(e2, *Tb)
                        if da is None or db is None:
                            continue
                        key = (da + db, math.hypot(Cc[0] - cx0, Cc[1] - cy0))
                        if best is None or key < best[0]:
                            best = (key, Cc, Ta, Tb, da, db)
                    if best is None:
                        break
                    _k, C, T1, T2, d1, d2 = best
                    if d1 <= 1e-6 and d2 <= 1e-6:
                        ok_t = True
                        break
                    if d1 <= 0.006 and d2 <= 0.006:
                        # касание чуть за краем кадра (соседний кадр почти касательный): конец скругления -
                        # в ближайшем конце кадра, излом там < 0.6°
                        def _clamp(e, T):
                            a0 = (e['x0'], e['y0']); a1 = (e['x1'], e['y1'])
                            return a0 if math.hypot(T[0] - a0[0], T[1] - a0[1]) <= math.hypot(T[0] - a1[0], T[1] - a1[1]) else a1
                        if d1 > 1e-6:
                            T1 = _clamp(e1, T1)
                        if d2 > 1e-6:
                            T2 = _clamp(e2, T2)
                        ok_t = True
                        break
                    if d1 > 1e-6:
                        if w1 == 0:
                            break
                        w1 -= 1
                    if d2 > 1e-6:
                        if w2 >= len(win) - 1:
                            break
                        w2 += 1
                if not ok_t:
                    break
                # дуга-скругление T1 -> T2 вокруг C: меньше 180°
                a1 = math.atan2(T1[1] - C[1], T1[0] - C[0])
                a2 = math.atan2(T2[1] - C[1], T2[0] - C[0])
                sw = (a1 - a2) % (2 * math.pi) if side > 0 else (a2 - a1) % (2 * math.pi)
                if sw >= math.pi - 1e-6:
                    break
                fmode = 2 if side > 0 else 3
                # от соседнего кадра не должен остаться микро-кусок: тогда скругление доводится до его конца
                if math.hypot(T1[0] - b1['x0'], T1[1] - b1['y0']) < min_len and w1 > 0:
                    T1 = (b1['x0'], b1['y0'])
                    w1 -= 1
                    b1 = win[w1]
                if math.hypot(b2['x1'] - T2[0], b2['y1'] - T2[1]) < min_len and w2 + 1 < len(win):
                    T2 = (b2['x1'], b2['y1'])
                    w2 += 1
                    b2 = win[w2]
                if math.hypot(T2[0] - T1[0], T2[1] - T1[1]) > 2 * rmin:
                    break
                # недорез: исходные точки между T1 и T2 до новой дуги
                seg = P[i + 1:j + 1]
                dv = float(_np.abs(_np.hypot(seg[:, 0] - C[0], seg[:, 1] - C[1]) - rmin).max()) if len(seg) else 0.0
                code = 'G%d X%s Y%s R%.5f' % (fmode, _nf_fmt(T2[0]), _nf_fmt(T2[1]), rmin)
                betw = win[w1 + 1:w2]
                set_end(b1, T1[0], T1[1])
                if betw:
                    nnum, _c, comment = _nf_split(lines[betw[0]['i']])
                    lines[betw[0]['i']] = nnum + code + ' ' + comment
                    for bb in betw[1:]:
                        delete.add(bb['i'])
                    fb = betw[0]
                    fb.update(mode=fmode, g=[float(fmode)], x0=T1[0], y0=T1[1], x1=T2[0], y1=T2[1],
                              w={'X': _nf_fmt(T2[0]), 'Y': _nf_fmt(T2[1]), 'R': '%.5f' % rmin}, code=code)
                else:
                    ins_after.setdefault(b1['i'], []).append(code + ' ;fix')
                # следующий кадр начинается в T2; его G-код - явно (после вставки модальность другая)
                b2['x0'], b2['y0'] = T2
                nnum, code2, comment2 = _nf_split(lines[b2['i']])
                if not any(g in _NF_MOTION_G for g in b2['g']):
                    lines[b2['i']] = nnum + 'G%d ' % b2['mode'] + code2.lstrip() + comment2
                    b2['g'] = b2['g'] + [float(b2['mode'])]
                if side == tool_side:
                    n_fil += 1
                else:
                    n_opp += 1
                n_arc += len([bb for bb in betw if bb['mode'] in (2, 3)])
                dev_fil = max(dev_fil, dv)
                done = True
                break
            k = kb + 1 if not done else max(k + 1, next((q for q, b in enumerate(act) if b is b2), k + 1))
    rmin = rmin_base

    # --- внутренние дуги (запасной способ: радиус до R_min при тех же концах) ---
    n_arc_old = 0
    for b in blocks if fix_radius else ():
        if b['i'] in delete or b['mode'] not in (2, 3) or 'R' not in b['w'] or b['x0'] is None:
            continue
        if b['ct'] in skip_ct or b['ct'] in circle_ct:
            continue
        inner = (b['comp'] == 42 and b['mode'] == 2) or (b['comp'] == 41 and b['mode'] == 3)
        if not (inner or (b['ct'] is not None and b['ct'] in sym_ct)):
            continue
        r_t = rmin if inner else r_opp
        R = float(b['w']['R'])
        if R < 0:
            if abs(R) < r_t:
                log.append('  ! стр.%d: дуга >180° R%.5f меньше R_min - исправить в CAM' % (b['i'] + 1, R))
            continue
        if R >= r_t - 1e-9:
            continue
        chord = math.hypot(b['x1'] - b['x0'], b['y1'] - b['y0'])
        if chord > 2 * r_t:
            continue
        maxdev = max(maxdev, _nf_sagitta(R, chord) - _nf_sagitta(r_t, chord))
        n_arc_old += 1
        nnum, code, comment = _nf_split(lines[b['i']])
        lines[b['i']] = nnum + re.sub(r'R-?\d*\.?\d+', 'R%.5f' % r_t, code, count=1) + comment
        n_arc += 1

    if n_opp:
        log.append('  дуги, внутренние для обратного прохода, < эквидистанты: %d мест -> касательная дуга R%.5f '
                   '(как делает CAM на обратном проходе)' % (n_opp, r_opp))
    if n_fil:
        log.append('  внутренние скругления < R%.4f: %d мест -> касательная дуга R%.4f (без изломов), '
                   'недорез до %.2f мкм' % (rmin, n_fil, rmin, dev_fil * 1000))
    if n_arc_old:
        log.append('  внутренних дуг R<%.4f (запасной способ, концы на месте): %d, недорез до %.2f мкм'
                   % (rmin, n_arc_old, maxdev * 1000))
    n_arc = n_arc + n_arc_old if n_fil else n_arc_old
    maxdev = max(maxdev, dev_fil)
    # --- точное замыкание: конец контура ровно в точке входа G12 (если отличается меньше min_len) ---
    n_close = 0
    for ctn, (sx, sy) in ct_start.items():
        if ctn in skip_ct:
            continue
        lastb = None
        for b in blocks:
            if b['ct'] == ctn and b['i'] not in delete:
                lastb = b
        if lastb is None or not plain(lastb):
            continue
        gap = math.hypot(lastb['x1'] - sx, lastb['y1'] - sy)
        if 0 < gap < 0.001:            # только расхождения меньше 1 мкм (заметные - не трогаем)
            if lastb['mode'] in (2, 3):
                R = float(lastb['w'].get('R', 0) or 0)
                if R <= 0 or math.hypot(sx - lastb['x0'], sy - lastb['y0']) > 2 * R:
                    continue
            set_end(lastb, sx, sy)
            n_close += 1
    if n_close:
        log.append('  замыкание контуров точно в точку входа: %d' % n_close)

    if n_straight:
        log.append('  прямые участки из мелких дуг/отрезков -> G1: %d (убрано кадров %d), откл. до %.2f мкм'
                   % (n_straight, n_str_blk, dev_str * 1000))
    if n_wig:
        log.append('  микро-перегибы (кадры < 20 мкм / дуги < R%.3f / изломы) -> G1: %d, откл. до %.1f мкм'
                   % (r_bad, n_wig, dev_wig * 1000))
    if n_micro:
        log.append('  микро-кадры < %.0f мкм удалены: %d, откл. до %.2f мкм' % (min_len * 1000, n_micro, dev_mic * 1000))
    if bad_micro:
        log.append('  ! микро-кадров не убрать без искажения: %d (стр. %s%s) - исправить в CAM'
                   % (len(bad_micro), ', '.join(map(str, bad_micro[:5])), '…' if len(bad_micro) > 5 else ''))
    n_micro += n_str_blk
    if not (n_arc or n_micro or n_fil or n_close):
        return None, log, (0, 0, 0.0)
    out = []
    for i, l in enumerate(lines):
        if i not in delete:
            out.append(l)
        out.extend(ins_after.get(i, ()))
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
        self._fix_deferred = False  # авто Fix ждёт окончания опроса (программы ещё выводятся)
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
        Label(f_btns, text='Enter:').pack(side=LEFT, padx=2)
        self.entr = Entry(f_btns, width=12, font=("Calibri", 11))
        self.entr.pack(side=LEFT, padx=2)
        Button(f_btns, text='✔', width=3, command=lambda: self.enter(self.entr.get())).pack(side=LEFT, padx=2)
        Button(f_btns, text='Папка', width=6, command=self.open_order_dir).pack(side=LEFT, padx=2)
        Button(f_btns, text='⚠ Столкновения', width=15, fg='red', command=self.check_intersections).pack(side=LEFT, padx=2)
        self.progress = Progressbar(f_btns, orient=HORIZONTAL, length=120, mode='determinate')
        self.progress.pack(side=LEFT, padx=5)
        Button(f_btns, text='Clear', width=8, command=self.clear).pack(side=RIGHT, padx=2)
        f_inp = Frame(self.left_panel)
        f_inp.pack(anchor=W, fill=X, pady=2)
        Button(f_inp, text='Open Dir', command=lambda: self.serchErr('')).pack(side=LEFT, padx=2)
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
        self.stop_btn = Button(f_inp, text='Стоп', width=5, command=lambda: self.stop_watch(run_fix=True))
        # кнопка показывается только во время опроса (см. start_watch)
        f_act = Frame(self.left_panel)
        f_act.pack(anchor=W, fill=X, pady=2)
        Button(f_act, text='Angle', command=lambda: self.repls(self.entr.get(), 1)).pack(side=LEFT, padx=2)
        Button(f_act, text='ABS', command=lambda: self.repls(self.entr.get(), 3)).pack(side=LEFT, padx=2)
        Button(f_act, text='Height', command=lambda: self.repls(self.entr.get(), 2)).pack(side=LEFT, padx=2)
        Button(f_act, text='add Comp', command=lambda: self.repls(self.entr.get(), 4)).pack(side=LEFT, padx=2)
        Button(f_act, text='Del Meas', command=self.del_meas).pack(side=LEFT, padx=2)
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
        # зум подложки: шаг 10%, не меньше 5% и не больше 10x (иначе размер картинки 0 -> ошибка)
        self.scale *= 1.1 if event.delta > 0 else 1 / 1.1
        self.scale = min(max(self.scale, 0.05), 10.0)
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
            size = max(1, int(iw * self.scale)), max(1, int(ih * self.scale))
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
            # self.ini(parName)     # комментарии по покупателю из anctor.xml - отключено
            self.text_com.insert(END, comment+'\n', "comma2")
            self.text_com.insert(END, comment2+'\n', "comma")
            # пользовательские комментарии (могут быть несколько, с временем)
            self.text_com.tag_config("comma3", foreground="blue")
            for uc in tree.getroot().iter('ПользовательскийКомментарий'):
                txt = (uc.text or '').strip()
                if not txt:
                    continue
                tm = uc.get('time', '').strip()
                self.text_com.insert(END, ('[%s] ' % tm if tm else '') + txt + '\n', "comma3")
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
        # авто Fix G-code - как автопроверка столкновений (не для Open Dir), до чтения файлов.
        # Если идёт опрос папки (программы ещё выводятся) - Fix один раз после окончания опроса,
        # чтобы захватить все программы и не трогать недописанные файлы.
        if mark and not from_dialog and self.settings.get('auto_fix') and os.path.isdir(tDir) \
                and not getattr(self, '_skip_auto_fix', False):
            if self._fix_deferred:
                self.settext('Авто Fix: выполнится после окончания опроса папки', 4)
            else:
                self.fix_gcode(d=tDir, auto=True)
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
            self._fix_deferred = bool(self.settings.get('auto_fix') and self.settings.get('poll_count', 0) > 0
                                      and self.settings.get('poll_interval', 0) > 0)
            self.serchErr(f)
            self.start_watch()            # опрос только для ручного ввода номера
            if self._fix_deferred and self._poll_job is None:   # опрос не запустился - Fix сразу
                self._run_deferred_fix()

    def _run_deferred_fix(self):
        """Авто Fix после опроса папки: все программы уже выведены. Затем папка перечитывается
        (превью, автопроверка столкновений), отчёт Fix выводится в конце лога."""
        self._fix_deferred = False
        if not self.settings.get('auto_fix') or not self.cur_dirs or not os.path.isdir(self.cur_dirs[0]):
            return
        if self._busy:                    # идёт проверка столкновений - подождать
            self._fix_deferred = True
            self.after(1000, self._run_deferred_fix)
            return
        self.fix_gcode(d=self.cur_dirs[0], auto=True, refresh=True)

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

    def stop_watch(self, run_fix=False):
        if self._poll_job is not None:
            try: self.after_cancel(self._poll_job)
            except Exception: pass
        self._poll_job = None
        self._poll_left = 0
        self.watch_lbl.config(text='')
        self.stop_btn.pack_forget()
        if self._fix_deferred:
            if run_fix:
                self._run_deferred_fix()
            else:
                self._fix_deferred = False

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
            self._poll_snap = dir_snapshot(self.cur_dirs[0])   # правки авто-Fix не считаем изменением
        if self._poll_left > 0:
            self._update_watch_lbl(changed)
            self._poll_job = self.after(t * 1000, self._poll_tick)
        else:
            fix = self._fix_deferred
            self.stop_watch(run_fix=True)
            self.watch_lbl.config(text='Опрос завершён' + (', выполнен авто Fix' if fix else ''))

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
        afix_var = IntVar(value=1 if self.settings.get('auto_fix') else 0)
        fa = Frame(win); fa.grid(row=4, column=0, columnspan=2, sticky=W, padx=10, pady=(6, 0))
        Checkbutton(fa, text='Автопроверка столкновений (*_R.anc, без revers)',
                    variable=auto_var).pack(anchor=W)
        Checkbutton(fa, text='Авто Fix G-code (перед проверкой, без вопросов)',
                    variable=afix_var).pack(anchor=W)
        fxh = Frame(win); fxh.grid(row=5, column=0, columnspan=2, sticky=W, padx=10, pady=(8, 0))
        Label(fxh, text='Fix G-code', font=("Calibri", 10, "bold")).pack(side=LEFT)
        frad_var = IntVar(value=1 if self.settings.get('fix_radius', 1) else 0)
        Checkbutton(fxh, text='коррекция малых радиусов (R_min, один на основные программы)',
                    variable=frad_var).pack(side=LEFT, padx=6)
        fmove_var = IntVar(value=1 if self.settings.get('fix_move_entry', 0) else 0)
        Checkbutton(win, text='Fix: переносить вход/выход контура из дуги на середину длинной прямой',
                    variable=fmove_var).grid(row=8, column=0, columnspan=2, sticky=W, padx=10)
        fx = Frame(win); fx.grid(row=6, column=0, columnspan=2, sticky=W, padx=10)
        fix_e = {}
        for r, (title, k) in enumerate((('Площадка: макс. + к номиналу, мм', 'fix_dtip'),
                                        ('Макс. угол заточки, °', 'fix_ang'),
                                        ('Страховка, мм', 'fix_safety'),
                                        ('Мин. радиус макета, все программы кроме 3D, мм', 'fix_rmin_all'))):
            Label(fx, text=title + ':').grid(row=r, column=0, sticky=W)
            e = Entry(fx, width=7); e.insert(0, '%g' % self.settings.get(k, 0))
            e.grid(row=r, column=1, padx=4, pady=2); fix_e[k] = e
        Label(fx, text='Программы мелких углов (в имени, через запятую):').grid(row=4, column=0, sticky=W)
        corner_e = Entry(fx, width=12); corner_e.insert(0, self.settings.get('fix_corner_mask', 'corner'))
        corner_e.grid(row=4, column=1, padx=4, pady=2)
        Label(fx, text='R_min = мин. радиус макета (0.5) для всех программ; 3D (ToolType = 1) не изменяются.\n'
                       'Если 0 - R_min по худшему инструменту: площадка +допуск, угол до макс., + страховка.',
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
            self.settings['auto_fix'] = afix_var.get()
            self.settings.update(fixv)
            self.settings['fix_corner_mask'] = corner_e.get().strip()
            self.settings['fix_backup'] = bak_var.get()
            self.settings['fix_radius'] = frad_var.get()
            self.settings['fix_move_entry'] = fmove_var.get()
            if not save_settings(self.settings):
                showerror('Настройки', 'Не удалось сохранить:\n' + SETTINGS_FILE, parent=win)
            win.destroy()
            self.entr.focus()

        bf = Frame(win); bf.grid(row=9, column=0, columnspan=2, pady=8)
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

    def fix_gcode(self, d=None, auto=False, refresh=False):
        """auto=True - авто Fix при проверке: папка задана, без вопросов, в лог только правки.
        После ручного Fix превью и проверка папки обновляются, отчёт Fix выводится заново."""
        if not auto or refresh:
            fix_lines = []
            _settext = self.settext
            def rec(text='', colo=0):
                fix_lines.append((text, colo))
                _settext(text, colo)
            self.settext = rec
            try:
                done_dir = self._fix_gcode(d, auto)
            finally:
                self.settext = _settext
            if done_dir and self.cur_dirs and os.path.normcase(os.path.normpath(self.cur_dirs[0])) == \
                    os.path.normcase(os.path.normpath(done_dir)):
                self._skip_auto_fix = True                         # Fix уже сделан - не повторять
                try:
                    self.serchErr('', resolved=self.cur_dirs)      # заново прочитать папку и превью
                except Exception as e:
                    self.settext('Не удалось обновить превью: %s' % e, 5)
                finally:
                    self._skip_auto_fix = False
                self.settext('')
                for t, c in fix_lines:                             # отчёт Fix - снова в лог
                    self.settext(t, c)
                self.text.see(END)
            return
        self._fix_gcode(d, auto)

    def _fix_gcode(self, d=None, auto=False):
        def note(text, err=True):
            if auto:
                self.settext('Авто Fix: ' + text.replace('\n', ' '), 5 if err else 4)
            elif err:
                showerror('Fix G-code', text)
            else:
                showinfo('Fix G-code', text)
        if self._busy:
            note('Дождитесь окончания текущей проверки.', False)
            return
        st = self.settings
        if d is None:
            d = self._fix_target_dir()
        if not d:
            return
        try:   # только файлы в самой папке, без вложенных
            files = sorted(os.path.join(d, n) for n in os.listdir(d)
                           if n.lower().endswith('.anc') and os.path.isfile(os.path.join(d, n)))
        except OSError as e:
            note('Нет доступа к папке:\n%s\n%s' % (d, e))
            return
        if not files:
            if not auto:
                note('В папке нет файлов .anc:\n' + d, False)
            return

        backup = bool(st.get('fix_backup', 1))
        dtip, ang_max = st.get('fix_dtip', 0.15), st.get('fix_ang', 90)
        safety, rmin_all = st.get('fix_safety', 0.03), st.get('fix_rmin_all', 0.5)
        bdir = os.path.join(d, NF_BACKUP_DIR)
        manifest = _nf_manifest(bdir) if os.path.isdir(bdir) else {}

        # --- проход 1: исходники (оригиналы, если файл - наша прошлая правка) и худший радиус ---
        cmask = st.get('fix_corner_mask', 'corner')
        items = []          # [path, name, cur, src, from_orig, группа]
        worst = {0: [], 1: [], 2: []}   # группа: 0 основные, 1 corner, 2 corner 3D -> [(r, name)]
        pre_warns = []
        rcs = {}            # группа -> [(эквидистанта/2, файл)]
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
                rc_f = nc_tool_data(txt)[0]
                if rc_f is not None:
                    rcs.setdefault(grp, []).append((rc_f, name))
            except Exception as e:
                note('Не прочитать файл:\n%s\n%s' % (path, e))
                return
        rmins, hows, warns = {}, {}, list(pre_warns)
        for grp, title in ((0, 'Основные'), (1, 'Мелкие углы (%s)' % cmask), (2, 'Мелкие углы 3D (ToolType = 1)')):
            if not any(it[5] == grp for it in items):
                continue
            if grp == 2:
                r, h = None, '3D - не изменяются'
            elif rmin_all > 0:
                r, h = rmin_all, 'мин. радиус макета'
            elif worst[grp]:
                r_max, n_max = max(worst[grp])
                r, h = r_max + safety, 'по %s: до %.4f + %.3f' % (n_max, r_max, safety)
            else:
                r, h = None, 'нет данных инструмента - не исправляются'
            rmins[grp] = None if r is None else math.ceil(r * 1e5 - 1e-6) / 1e5
            n = sum(1 for it in items if it[5] == grp)
            hows[grp] = ('%s (%d): R_min %.5f, %s' % (title, n, rmins[grp], h)) if r is not None else '%s (%d): %s' % (title, n, h)

        fix_r = bool(st.get('fix_radius', 1))
        if not fix_r:
            hows = {0: 'Коррекция малых радиусов ВЫКЛЮЧЕНА - радиусы как в макете'}
            warns = [w for w in warns if 'corner-инструмента' not in w]
        msg = ('Папка:\n%s\n\nФайлов .anc: %d\n\n%s\n'
               % (d, len(files), '\n'.join(hows[g] for g in (0, 1, 2) if g in hows)))
        if fix_r and rmin_all <= 0:
            msg += '(площадка +%.3f, угол до %g°)\n' % (dtip, ang_max)
        if warns:
            msg += '\n' + '\n'.join(warns) + '\n'
        msg += ('\nОригиналы: %s (правка всегда от оригинала)\n' % NF_BACKUP_DIR) if backup else '\nОригиналы НЕ сохраняются!\n'
        msg += '\nИсправить файлы?'
        if not auto and not self.question('Fix G-code', msg):
            return

        # --- проход 2: правка всех файлов с одним R_min ---
        self._busy = True
        self.fix_btn.config(state=DISABLED)
        if not auto:
            self.settext('')
        self.settext(('=== Авто Fix G-code ===' if auto else '=== Fix G-code: %s ===' % d), 4)
        for g in (0, 1, 2):
            if g in hows:
                self.settext(hows[g], 4)
        for w in warns:
            self.settext(w, 1)
        self.progress['maximum'] = len(items)
        self.progress['value'] = 0
        n_files = n_arcs = n_micro = n_err = n_rest = 0
        # пары прямой/обратный проход одной геометрии (в одном файле или в разных файлах папки):
        # правится первый проход, второй строится как его точное обращение - геометрия совпадает
        def step(txt):
            self.lbl.config(text='Fix G-code: ' + txt)
            self.progress['value'] = self.progress['value'] + 1
            self.update_idletasks()
        self.progress['maximum'] = 3 * len(items) + 1
        texts = {it[1]: it[3].decode('latin-1') for it in items}
        move_logs, moved_files = {}, set()
        if st.get('fix_move_entry', 0):
            orig_start = {}
            for it in items:
                if it[5] != 2:
                    for ct, c in nc_contours(texts[it[1]]).items():
                        orig_start[(it[1], ct)] = c['start']
            for it in items:
                if it[5] == 2:                 # 3D не трогаем
                    continue
                step('перенос входа ' + it[1])
                mt, mlog, mn = nc_move_entries(texts[it[1]])
                if mt is not None:
                    texts[it[1]] = mt
                    moved_files.add(it[1])
                if mlog:
                    move_logs[it[1]] = mlog
            # пары прямой/обратный проход: обратный - в ту же точку входа, что и прямой
            if moved_files:
                cts_all = {}
                for it in items:
                    if it[5] != 2:
                        for ct, c in nc_contours(texts[it[1]]).items():
                            cts_all[(it[1], ct)] = c
                tg = {}
                for (fa, ca), (fb, cb) in nc_find_pairs(cts_all):
                    if fa not in moved_files and fb not in moved_files:
                        continue
                    # только пары, у которых CAM поставил вход в одну точку (её и надо сохранить общей)
                    oa, ob = orig_start.get((fa, ca)), orig_start.get((fb, cb))
                    if oa is None or ob is None or math.hypot(oa[0] - ob[0], oa[1] - ob[1]) > 0.01:
                        continue
                    sa, sb = cts_all[(fa, ca)]['start'], cts_all[(fb, cb)]['start']
                    if math.hypot(sa[0] - sb[0], sa[1] - sb[1]) > 1e-3:
                        tg.setdefault(fb, {})[cb] = sa
                for fb, tgt in tg.items():
                    mt, mlog, mn = nc_move_entries(texts[fb], targets=tgt)
                    if mt is not None:
                        texts[fb] = mt
                        moved_files.add(fb)
                    if mn < len(tgt):
                        move_logs.setdefault(fb, []).append(
                            '  ! обратных проходов не удалось перенести в точку входа прямого: %d' % (len(tgt) - mn))
        grp_of = {it[1]: it[5] for it in items}
        conts = {}
        for nm, tx in texts.items():
            step('разбор ' + nm)
            if grp_of[nm] == 2:            # 3D не трогаем
                continue
            for ct, c in nc_contours(tx).items():
                conts[(nm, ct)] = c
        pairs = [(a, b) for a, b in nc_find_pairs(conts) if grp_of[a[0]] == grp_of[b[0]]]
        skip, sym, prot = {}, {}, {}
        for (fa, ca), (fb, cb) in pairs:
            sym.setdefault(fa, set()).add(ca)
            skip.setdefault(fb, set()).add(cb)
            prot.setdefault(fa, []).append(conts[(fb, cb)]['start'])
        results = {}
        for it in items:
            nm, grp = it[1], it[5]
            if rmins.get(grp) is None:
                continue
            step('исправление ' + nm)
            nt, lg, st3 = nc_fix_text(texts[nm], min_radius=rmins[grp], skip_ct=skip.get(nm, ()),
                                       sym_ct=sym.get(nm, ()), protect=prot.get(nm, ()), fix_radius=fix_r)
            if nt is None and nm in moved_files:
                nt = texts[nm]                 # перенесён только вход
            results[nm] = [nt, move_logs.get(nm, []) + lg, st3]
        n_pair_ok, rebuilt = 0, {}
        # образцы: исправленные прямые проходы (каждый файл разбирается один раз)
        canon_c = {}
        for fa in set(p[0][0] for p in pairs):
            step('пары ' + fa)
            canon_c[fa] = nc_contours(results[fa][0] if results[fa][0] is not None else texts[fa])
        jobs = {}
        for (fa, ca), (fb, cb) in pairs:
            jobs.setdefault(fb, {})[cb] = (canon_c[fa].get(ca), fa, ca)
        for fb, jb in jobs.items():
            step('обратные проходы ' + fb)
            tb = results[fb][0] if results[fb][0] is not None else texts[fb]
            nt, errs = nc_rebuild_reverse(tb, {cb: v[0] for cb, v in jb.items()})
            for cb, why in errs.items():
                results[fb][1].append('  ! обратный проход (контур %d) не приведён к геометрии %s/%d: %s'
                                      % (cb, jb[cb][1], jb[cb][2], why))
            if nt is not None and nt != tb:
                results[fb][0] = nt
            ok_n = len(jb) - len(errs)
            n_pair_ok += ok_n
            if ok_n:
                rebuilt[fb] = ok_n
        for fb, n in rebuilt.items():
            results[fb][1].append('  обратных проходов построено по прямому (общая геометрия): %d' % n)
        # явный G2/G3 в дугах входа/выхода нового постпроцессора (модальность не должна поменяться)
        for it in items:
            if it[1] in results and results[it[1]][0] is not None:
                results[it[1]][0] = nc_explicit_leads(results[it[1]][0], it[3].decode('latin-1'))
                # CLN(DLAn) контура = число кадров контура - 2 (не больше общего DLA) - после правок пересчитать
                results[it[1]][0], n_dla = nc_update_dla(results[it[1]][0])
                if n_dla:
                    results[it[1]][1].append('  CLN(DLA) пересчитан под новое число кадров: %d контуров' % n_dla)
        self.lbl.config(text=d)
        self.progress['maximum'] = len(items)
        self.progress['value'] = 0
        if pairs:
            self.settext('Пар прямой/обратный проход: %d (геометрия общая)' % n_pair_ok, 4)
        try:
            for k, (path, name, cur, src, from_orig, grp) in enumerate(items, 1):
                try:
                    bpath = os.path.join(bdir, name)
                    have_b = os.path.isfile(bpath)
                    if rmins.get(grp) is None:
                        self.settext(name + (': 3D - не изменяется' if grp == 2 else
                                             ': пропущен (нет данных инструмента)'), 4 if grp == 2 else 1)
                        continue
                    name_l = name + ('', ' [corner]', ' [corner 3D]')[grp]
                    new_text, log, (a, mc, dev) = results[name]
                    out = src if new_text is None else new_text.encode('latin-1')
                    if out == cur:
                        log = [l for l in log if '!' in l or 'ВНИМАНИЕ' in l]   # правок нет - только предупреждения
                        if not (auto and not log):      # в авто-режиме OK-файлы не перечисляем
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
                            self.settext('%s: ИСПРАВЛЕН (дуг %d, убрано кадров %d)%s'
                                         % (name_l, a, mc, ' - от оригинала' if from_orig else ''), 4)
                    for l in log:
                        self.settext(l, 4 if '!' in l or 'ВНИМАНИЕ' in l else 0)   # предупреждения - синим
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
        if not auto:
            self.settext('')
        self.settext('ИТОГО: файлов %d, исправлено %d (дуг %d, убрано кадров %d), восстановлено %d, ошибок %d'
                     % (len(items), n_files, n_arcs, n_micro, n_rest, n_err), 4)
        if self._poll_job is not None and self.cur_dirs and self.cur_dirs[0] == d:
            self._poll_snap = dir_snapshot(d)   # свои правки не считаем изменением папки
        if not auto:
            self.text.see(END)
        return d

    def open_order_dir(self):
        """Открыть в проводнике папку текущего заказа (с выделенной папкой NC).
        Папка - последняя проверенная, иначе по номеру в поле Enter."""
        nc = None
        if self.cur_dirs and self.cur_dirs[0]:
            nc = os.path.normpath(self.cur_dirs[0])
        else:
            w = self.entr.get().strip()
            if w:
                nc = "\\\\storage\\Zakaz\\" + w[0:-3] + "000-" + w[0:-3] + "999\\" + w + "\\" + w + "-NC"
        if not nc:
            showinfo('Папка заказа', 'Введите номер заказа или проверьте папку.')
            return
        order = os.path.dirname(nc) if '-NC' in os.path.basename(nc).upper() else nc
        try:
            import subprocess
            if os.path.isdir(nc) and order != nc:
                subprocess.Popen('explorer /select,"%s"' % nc)   # папка заказа, NC выделена
            elif os.path.isdir(order):
                os.startfile(order)
            else:
                showinfo('Папка заказа', 'Папка не найдена:\n%s' % order)
        except Exception as e:
            showerror('Папка заказа', 'Не удалось открыть папку:\n%s\n%s' % (order, e))
        self.entr.focus()

    def del_meas(self):
        """Удалить измерения щупом (Altitude measurement / IHOC) во всех .anc папки заказа.
        Имена файлов не меняются, оригиналы не сохраняются."""
        if self._busy:
            showinfo('Del Meas', 'Дождитесь окончания текущей проверки.')
            return
        w = self.entr.get().strip()
        d = None
        if w:
            d = "\\\\storage\\Zakaz\\" + w[0:-3] + "000-" + w[0:-3] + "999\\" + w + "\\" + w + "-NC"
        elif self.cur_dirs:
            d = self.cur_dirs[0]
        if not d or not os.path.isdir(d):
            showinfo('Del Meas', 'Папка NC не найдена:\n%s' % d)
            return
        files = sorted(os.path.join(d, n) for n in os.listdir(d)
                       if n.lower().endswith('.anc') and os.path.isfile(os.path.join(d, n)))
        found = {}
        for path in files:
            try:
                with open(path, 'rb') as f:
                    txt = f.read().decode('latin-1')
            except OSError:
                continue
            n = sum(1 for l in txt.split('\n') if 'Altitude measurement' in l)
            if n:
                found[path] = (txt, n)
        if not found:
            showinfo('Del Meas', 'Измерений в программах нет:\n%s' % d)
            return
        msg = 'Папка:\n%s\n\nПрограммы с измерениями:\n%s\n\nУдалить измерения? (оригиналы не сохраняются)' % (
            d, '\n'.join('  %s - %d' % (os.path.basename(p), v[1]) for p, v in found.items()))
        if not self.question('Del Meas', msg):
            return
        self.settext('')
        self.settext('=== Del Meas: %s ===' % d, 4)
        done = 0
        for path, (txt, n) in found.items():
            crlf = '\r\n' in txt
            lines = txt.replace('\r\n', '\n').split('\n')
            out = [l for l in lines if not nc_is_meas_line(l)]
            try:
                tmp = path + '.meastmp'
                with open(tmp, 'wb') as f:
                    f.write(('\r\n' if crlf else '\n').join(out).encode('latin-1'))
                os.replace(tmp, path)
                done += 1
                self.settext('%s: удалено измерений %d (строк %d)' % (os.path.basename(path), n, len(lines) - len(out)), 1)
            except OSError as e:
                self.settext('%s: ОШИБКА %s' % (os.path.basename(path), e), 5)
        self.settext('ИТОГО: программ исправлено %d' % done, 4)
        if self._poll_job is not None and self.cur_dirs and self.cur_dirs[0] == d:
            self._poll_snap = dir_snapshot(d)
        self.text.see(END)
        self.entr.focus()

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
