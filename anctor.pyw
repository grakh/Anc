from tkinter import *
from tkinter.messagebox import *
from tkinter.filedialog import *
from xml.etree.ElementTree import parse
import os, sys
import glob
import pprint
import sqlite3

#root=Tk()
#root.title("Test")
#root.geometry("500x750")
allanc = []
mark = False
ver = 'Anctor V2.6'

#frm = Frame(root)
#qt = Frame(root)

class ErrAnc(Frame):
    def __init__(self, parent=None):
        Frame.__init__(self, parent)
        self.parent = parent
        #root.bind('<Return>', self.enter)
        self.initUI()

    def initUI(self):
        self.master.title("Testing...")
        self.pack(fill=BOTH, expand=True)

        self.columnconfigure(1, weight=1)
        self.columnconfigure(4, pad=1)
        self.rowconfigure(8, weight= 1)
        self.rowconfigure(12, pad=10)

        self.lbl = Label(self, text="Windows")
        self.lbl.grid(sticky=W, pady=5, padx=5)

        self.com_widgets()
        self.makewidgets()

        Button(self, text='☼',  command=self.infobox).grid(row=0, column=4, pady=4,  padx=5, sticky=E)
        Button(self, text='Open Dir', command= lambda: self.serchErr('')).grid(row=1, column=4, pady=5, padx=4, sticky=E+W+N)
        Button(self, text='Clear',  command=self.help).grid(row=2, column=4, pady=5,  padx=4, sticky=E+W+N)

        entr_namb = Entry(self, width=12, font=("Calibri", 14))
        entr_namb.grid(row=3, column=4, pady=[30, 5],  padx=4, ipady=1)
        entr_namb.focus()
        bt = Button(self, text='Enter', command = lambda: self.enter(entr_namb.get()))
        bt.grid(row=4, column=4, pady=5,  padx=4, sticky=E+W+N)
        #Label(self, text='XML:').grid(row=8, column=4, pady=4,  padx=5, sticky=W)
        self.displayA = Label(self, text='compare with XML', bg='yellow')
        self.displayA.grid(row=9, column=4, pady=4,  padx=5, sticky=W)
        self.displayH = Label(self)
        self.displayH.grid(row=10, column=4, pady=4,  padx=5, sticky=W)

        Button(self, text='Quit',  command=self.quit).grid(row=12, column=4, padx=4, pady=5, sticky=E+W+S)

        entr_namb.bind("<Return>", lambda e, f=entr_namb.get(): self.enter(entr_namb.get()))
        self.entr = entr_namb

    def makewidgets(self):
        sbar = Scrollbar(self, orient = VERTICAL)
        text = Text(self, relief=RIDGE, height=20)
        sbar.config(command=text.yview)                  # xlink sbar and text
        text.config(yscrollcommand=sbar.set)             # move one moves other
        sbar.grid(row=1, column=2, rowspan=8, padx=5, pady=5, sticky=S+N)
        text.grid(row=1, column=0, columnspan=2, rowspan=8, padx=5, pady=5, sticky=E+W+S+N)
        self.text = text

    def com_widgets(self):
        sbar_com = Scrollbar(self, orient = VERTICAL)
        text_com = Text(self, relief=RIDGE, height=5)
        sbar_com.config(command=text_com.yview)                  # xlink sbar and text
        text_com.config(yscrollcommand=sbar_com.set)             # move one moves other
        sbar_com.grid(row=9, column=2, rowspan=4, sticky=S+N)
        text_com.grid(row=9, column=0, rowspan=4, columnspan=2, padx=5, pady=5, sticky=E+W+S+N)
        self.text_com = text_com

    def settext(self, text='', colo=0):
		#self.text.delete('1.0', END)                     # delete current text
		#self.text.tag_add("here", "2.0", "2.4")
        self.text.tag_config("here", foreground="red")
        self.text_com.tag_config("comma", foreground="red")
        self.text_com.tag_config("comma2", foreground="green")
        self.text.tag_config("XMLhere", background="yellow")
        self.text.tag_config("PPC", foreground="red", background="yellow")
        self.text.tag_config("info", foreground="blue")
        if colo==1:
            self.text.insert(END, text+'\n', "here")        # add at line 1, col 0
        elif colo==2:
            self.text.insert(END, text+'\n', "XMLhere")        # add at line 1, col 0
        elif colo==3:
            self.text.insert(END, text+'\n', "PPC")        # add at line 1, col 0
        elif colo==4:
            self.text.insert(END, text+'\n', "info")
        else:
            self.text.insert(END, text+'\n')        # add at line 1, col 0
		#self.text.mark_set(INSERT, '1.0')                # set insert cursor
        self.text.focus()                                # save user a click

    def gettext(self):                                   # returns a string
        return self.text.get('1.0', END+'-1c')           # first through last

    def openDir(self):
        global mark
        if len(sys.argv) < 2:
            self.help()
            mark = True
            dirname = askdirectory(mustexist=True, title='Please select a directory')
			#if len(dirname)<=0:
				#dirname = = os.getcwd()


        else:
            dirname = sys.argv[1]

		#allanc = glob.glob(dirname + os.sep + '*.anc')

        dirname = os.path.normpath(dirname)
        self.lbl.config(text=dirname)
        self.puts("You chose %s" % dirname)
        self.puts('='*30)
        self.puts()
        return dirname

    def puts(self, txt='', colo=0):
        global mark
		#print(mark)
        if mark:
            self.settext(txt, colo)
        else:
            if colo==1:
                print('Error: '+txt)
            elif colo==2 or colo==3:
                print('XML Error: '+txt)
            else:
                print(txt)

    def displ(self, anXML, hiXML, comment='gnr'):
        self.displayA.config(text = 'Angle: {}'.format(anXML), bg='lightblue')
        self.displayH.config(text = 'Height: {}'.format(hiXML), bg='lightblue')
		#self.displayC.config(text = 'Comment: {}'.format(comment))

    def ini(self, partentName):
        path_ini = os.path.normpath(os.path.dirname(os.path.abspath(__file__)) + "\\anctor.xml")
        #self.errorbox(path_ini)
        try:
            ini_tree = parse(path_ini)
            com_ini = ''
        except:
            
            self.text_com.insert(END, 'No such file! '+ path_ini, "comma")

        for childs in ini_tree.findall('firm'):
            com_ini = childs.find('comm').text
            name = childs.get('name')
            if name == partentName:
                self.text_com.insert(END, com_ini+'\n', "comma")

    def XMLP(self, dir):
        hereDir = dir[:dir.rfind('-NC\\')]
        hereDir = hereDir[:hereDir.rfind('\\')]
        #self.errorbox(hereDir)
        namberFile = 'specification_'+hereDir[hereDir.rfind('\\')+1:]+'.xml'
        try:
            xmlFile = os.path.join(hereDir+'\\XML', namberFile)

            tree = parse(xmlFile)

            for height in tree.findall('ВысотаНожа'):
                hiXML = height.text

            for anl in tree.findall('УголЗаточкиКромки'):
                anXML = anl.text


        except:
            self.puts('No such file “%s”!' % namberFile)
			#self.errorbox ('No such file “%s”!' % namberFile)

        try:
            tree.getroot().attrib['Комментарий']
            tree.getroot().attrib['КомментарийКонтрагента']
            comment = tree.getroot().attrib['КомментарийКонтрагента']
            comment2 = tree.getroot().attrib['Комментарий']
            tree.getroot().attrib['Покупатель']
            parName = tree.getroot().attrib['Покупатель']
            #self.errorbox(parName)
        except:
            comment =''
        self.text_com.delete('1.0', END)
        self.master.title(parName)
        self.ini(parName)
        self.text_com.insert(END, comment+'\n', "comma2")
        self.text_com.insert(END, comment2+'\n', "comma")

        if len(sys.argv) < 2:
            self.displ(anXML, hiXML, comment2)

        return anXML, hiXML

    def serchErr(self, tDir):
        allanc=[]
        angle=[]
        mr=''
        if tDir == '':
            tDir=self.openDir()
            #showerror('', tDir)
        else:
            global mark
            self.help()
            mark = True
            tDir = "\\\storage\Zakaz\\" + tDir[0:-3]+"000-"+ tDir[0:-3]+"999\\"+tDir+"\\"+tDir+"-NC"
            self.lbl.config(text=tDir)
            self.puts("You chose %s" % tDir)
            self.puts('='*30)
            self.puts()

        for (fileHere) in os.listdir(tDir):
			#print(thisDir)
			#print(subHere)
			#print(fileHere)
            #showinfo(thisDir, fileHere)
            if fileHere==[]:
                continue
            if fileHere.endswith('.anc'):
                fullname = os.path.join(tDir, fileHere)
                #fullsize = os.path.getsize(fullname)
				#allanc.append((fullsize, fullname))
                #showinfo(tDir, fullname)
                allanc.append(fullname)


        angleXML, heightXML = self.XMLP(tDir)
			#print (mr)
		#allanc.sort()
		#pprint.pprint(allanc)
        for files in allanc:
            fl = files[files.rfind('\\')+1:]
            angle = fl.split('_')
			#print(angle)
            mr = fl[fl.rfind('_')+1:fl.rfind('.')]
            i=0
            j=0
            lp=0
            LSD = False
            EOFP = False
            namber_cut = 0
            compesation_cut = 0
            Drill = False
            ToolCompMode = False

            self.puts(files)
            for line in open(files):
                if 'SSDE[SD.WZRec.UD.Ed[1].Geo.Ang' in line:
                    angl = line[line.find('=')+2:-3]
                    k=0
                    if angle[1]!=angl:
                        k=1
                    if angl!=angleXML:
                        k+=2
                    self.puts('Angle = %s' % angl, k)
                if 'ProgDieHeight' in line:
                    hi = line[line.find('=')+2:line.find(']')]
                    if hi!=heightXML:
                        self.puts('Height = %s' % hi, 2)
                    else:
                        self.puts('Height = %s' % hi, 0)
                if 'ZPosDiaMeas' in line:
                    dp = line[line.find('= ABS(')+6:line.find(']')-1]
					#print(dp)
                    if dp == '0.25':
                        self.puts('Depth = %s' % dp, 0)
                    else:
                        self.puts('Depth = %s' % dp, 1)
                if 'Altitude' in line:
                    i+=1
                if 'TOOL DATAS' in line:
                    j+=1
                if 'Begin of Contour' in line:
                    EOFP = True
                    #LSD = True
                if 'Begin of Loop' in line and EOFP:
                    LSD = False
                    EOFP = False
                if 'PREPART' in line:
                    namber_cut +=1
                    compesation_cut = 1

                if 'G42' in line or 'G41' in line:
                    compesation_cut = 0
				
                if 'G1 Z0.1' in line:
                    Drill = True

                if 'ToolCompMode = 1' in line:
                    ToolCompMode = line[line.find('ToolCompMode =')+15:line.find(']')]

            if compesation_cut:
                self.puts("Knives = %s without compensation" % namber_cut, compesation_cut)

			#print(mr)
            if i>0:
                if mr=='M':
                    self.puts('Measurement file')
                    self.puts('Number of measurements %s' % i)
                else:
                    self.puts('Measurement file', 1)
                    self.puts('Number of measurements %s' % i, 1)

            else:
                if mr=='R':
                    self.puts('File without measurements')
                else:
                    self.puts('File without measurements', 1)

            if j>1:
                self.puts('Label Tool Data', 3)
            if LSD:
                self.puts('Label Shape Data', 3)

            if Drill:
                self.puts('Drill is true', 4)

            if ToolCompMode:
                self.puts('ToolCompMode = %s' % ToolCompMode, 3)
				
            self.puts('-'*30)
            self.puts()

            self.entr.focus()

    def infobox(self, e=0, title='Настойки', text=ver, *args):              # use standard dialogs
        return showinfo(title, text)                    # *args for bkwd compat

    def errorbox(self, text):
        showerror('Error!', text)

    def question(self, title, text, *args):
        return askyesno(title, text)                    # return True or False

    def notdone(self):
        showerror('Not implemented', 'Option not available')

    def quit(self):
        ans = self.question('Verify quit', 'Are you sure you want to quit?')
        if ans:
            Frame.quit(self)                            # quit not recursive!

    def help(self):
		#self.infobox('RTFM', 'See figure 1...')         # override this better
        self.text.delete('1.0', END)
        self.text_com.delete('1.0', END)
        self.entr.delete(0, 'end')

    def enter(self, f):
        if f == '':
            self.serchErr('')
        else:
            self.serchErr(f)


if __name__ == '__main__':

	if len(sys.argv) < 2:
		root = Tk()
		root.geometry("550x700")
		app = ErrAnc(root)
		root.mainloop()
	else:
		st = ErrAnc()
		st.serchErr()
		input('Press any key...')
