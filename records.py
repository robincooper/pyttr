from collections import deque
from utils import show,to_latex,ttracing,substitute

class Rec(object):
    def __init__(self,d={}):
        for item in d.items():
            if isinstance(item[1], dict):
                self.addfield(item[0], Rec(item[1]))
            else:
                self.addfield(item[0], item[1])
            
    def show(self):
        s = ""
        for kvp in self.__dict__.items():           
            if s == "":
                s = s + kvp[0] + " = "
            else:
                s = s + ", "+kvp[0] + " = "
            
            if(isinstance(kvp[1], Rec)):
                 s = s + kvp[1].show()                
            else:
                s = s + show(kvp[1]) 
        return "{"+s+"}"
        
    def to_latex(self,vars):
        s = ""
        for kvp in self.__dict__.items():           
            if s == "":
                s = s + to_latex(kvp[0]) + " &=& "
            else:
                s = s + "\\\\\n"+to_latex(kvp[0]) + " &=& "
            
            if(isinstance(kvp[1], Rec)):
                 s = s + kvp[1].to_latex(vars)
            else:
                s = s + to_latex(kvp[1],vars)
                
        return "\\left[\\begin{array}{rcl}\n"+s+"\n\\end{array}\\right]"
        
    def addfield(self, label, value):
        if label in self.__dict__.keys(): 
            print("\"" +label + "\"" + " is already a label in " +show(self))
        else: 
            self.__setattr__(label, value)
            return self

    def addpath(self, path, value):
        pathl = path.split(".")
        return self.addpathl(pathl, value)

    def addpathl(self, pathl, value):
        if len(pathl) == 1:
            return self.addfield(pathl[0],value)
        elif pathl[0] in self.__dict__.keys():
            val = self.__getattribute__(pathl[0])
            if isinstance(val, Rec):
                val.addpathl(pathl[1:], value)
            else:
                print(val + ' is not a record.')
            return self
        else:
            self.addfield(pathl[0], Rec().addpathl(pathl[1:],value))
            return self
            
    
    # def pathvalue(self,path):
    #     if len(path) == 1: 
    #         return self.__getattribute__(str(path[0]))
    #     else: 
    #         return Rec.pathvalue(self.__getattribute__(path[0]), path[1:])
            
    def pathvalue(self, path):
        splits=deque(path.split("."))
        if (len(splits) == 1):
            if splits[0] in dir(self):
                return self.__getattribute__(splits[0])
            else:
                if ttracing('pathvalue'):
                    print(splits[0]+' not a label in '+self.show())
                return None
        else:
            addr = splits.popleft()
            if addr not in dir(self):
                if ttracing('pathvalue'):
                    print('No attribute '+addr+' in '+show(self))
                return None
            elif 'pathvalue' not in dir(self.__getattribute__(addr)):
                if ttracing('pathvalue'):
                    print('No paths into '+show(self.__getattribute__(addr)))
                return None
            else:
                return self.__getattribute__(addr).pathvalue(".".join(splits))
    
    #Recursive for future use
    #Needs redefining so as not to be destructive?
    def relabel(self, oldlabel, newlabel):
        newrec = Rec(self.__dict__)
        if oldlabel in newrec.__dict__.keys():
            value = newrec.__dict__[oldlabel]
            newrec.__delattr__(oldlabel)
            newrec.__setattr__(newlabel, value)
        return newrec
    
    def subst(self,v,a):
        res = Rec()
        for l in self.__dict__.keys():
            lval = self.__getattribute__(l)
            if lval == v:
                res.addfield(l,a)
            elif isinstance(lval,str):
                res.addfield(l,lval)
            else: 
                res.addfield(l,substitute(lval,v,a))
        return res

    def eval(self):
        for l in self.__dict__.keys():
            lval = self.__getattribute__(l)
            if 'eval' in dir(lval):
                self.__setattr__(l,lval.eval())
        return self
                
    def flatten(self):
        res = Rec()
        for l in self.__dict__.keys():
            lval = self.__getattribute__(l)
            if isinstance(lval,str):
                res.addfield(l,lval)
            elif isinstance(lval,Rec):
                rec1 = lval.flatten()
                for l1 in rec1.__dict__.keys():
                    res.addfield(l+"."+l1,rec1.__getattribute__(l1))
        return res

    def unflatten(self):
        res = Rec()
        for l in self.__dict__.keys():
            res.addpath(l, self.__getattribute__(l))
        return res

    def addrec(self,r):
        res = Rec()
        for l in [l for l in self.__dict__ if not l in r.__dict__]:
            res.addfield(l,self.__getattribute__(l))
        for l in [l for l in self.__dict__ if l in r.__dict__]:
            rl = r.__getattribute__(l)
            #print('rl: ',show(rl))
            sl = self.__getattribute__(l)
            #print('sl: ',show(sl))
            if isinstance(rl, Rec) and isinstance(sl,Rec):
                res1 = sl.addrec(rl)
                #print('res1: ',show(res1))
                if res1:
                    res.addfield(l,res1)
                else:
                    return None
            elif rl == sl:
                res.addfield(l,rl)
            else:
                return None
        for l in [l for l in r.__dict__ if not l in self.__dict__]:
            res.addfield(l,r.__getattribute__(l))
        return res
 

    
