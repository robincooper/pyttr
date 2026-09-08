from collections import deque

from .model import _M
from .records import Rec
from .terms import AbsPath, HypObj
from .type_core import TypeClass, logtype, logtype_t
from .type_ops import combine_dep_types, merge_dep_types, subtype_of_dep_types
from .utils import forall, forsome, show, substitute, to_latex, ttracing

class RecType(TypeClass):
    def __init__(self,d=None):
        if d is None:
            d = {}
        self.comps = Rec()
        for item in d.items():
            if isinstance(item[1], dict):
                self.addfield(item[0], RecType(item[1]))
            else:
                self.addfield(item[0], item[1])
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [ \
            lambda r: isinstance(r, Rec) and RecOfRecType(r,self,self.poss)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        s = ""
        for kvp in self.comps.items():
            if s == "":
                s = s + kvp[0] + " : "
            else:
                s = s + ", "+kvp[0] + " : "
            
            if(isinstance(kvp[1], RecType)):
                 s = s + kvp[1].show()                
            else:
                s = s + show(kvp[1]) 
        return "{"+s+"}"
    
    def to_latex(self,vars):
        s = ""
        for kvp in self.comps.items():
            if s == "":
                s = s + to_latex(kvp[0]) + " &:& "
            else:
                s = s + "\\\\\n"+to_latex(kvp[0]) + " &:& "
            
            if(isinstance(kvp[1], RecType)):
                 s = s + kvp[1].to_latex(vars)                
            else:
                s = s + to_latex(kvp[1],vars,anglebrackets="yes") 
        return "\\left[\\begin{array}{lcl}\n"+s+"\n\\end{array}\\right]"

    def validate(self):
        if forall(list(self.comps.items()),lambda x: CheckField(x,self)) and self.create_hypobj() is not None:
            return True
        else:
            return False
        
        
    def addfield(self, label, value):
        if label in self.comps:
            print("\"" +label + "\"" + " is already a label in this record type")
        else: 
            self.comps.addfield(label, value)
    def pathvalue(self, path):
        splits=deque(path.split("."))
        if (len(splits) == 1):
            if splits[0] in self.comps:
                return self.comps[splits[0]]
            else:
                if ttracing('pathvalue'):
                    print(splits[0]+' not a label in '+self.show())
                return None
        else:
            addr = splits.popleft()
            if addr not in self.comps:
                if ttracing('pathvalue'):
                    print('No attribute '+addr+' in '+show(self.comps))
                return None
            elif not hasattr(self.comps[addr], 'pathvalue'):
                if ttracing('pathvalue'):
                    print('No paths into '+show(self.comps[addr]))
                return None
            else:
                return self.comps[addr].pathvalue(".".join(splits))
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def create(self):
        res = Rec()
        depfields = RecType()
        for l in self.comps:
            T = self.comps[l]
            if isinstance(T,TypeClass):
                res.addfield(l,T.in_poss(self.poss).create())
            else: depfields.addfield(l,T)
        return ProcessDepFields(depfields,res,self)
        
    def create_hypobj(self):
        res = Rec()
        depfields = RecType()
        for l in self.comps:
            T = self.comps[l]
            if isinstance(T,TypeClass):
                res.addfield(l,T.create_hypobj())
            else: depfields.addfield(l,T)
        return ProcessDepFields(depfields,res,self,'hyp')
        

        
    
    #Recursive for future use??            
    def Relabel(self, oldlabel, newlabel, recursive=False):
        if oldlabel in self.comps:
            value = self.comps.pop(oldlabel)
            self.comps[newlabel] = value
        return
    
    def subst(self,v,a):
        res = RecType()
        for l in self.comps:
            lval = self.comps[l]
            if lval == v:
                res.addfield(l,a)
            elif isinstance(lval,str):
                res.addfield(l,lval)
            else: 
                res.addfield(l,substitute(lval,v,a))
        #print(show(res))
        return res

    def eval(self):
        self.comps.eval()
        return self

    def merge(self,T):
        if isinstance(T,RecType):
            res = RecType({})
            SharedLabels = [l for l in LabelsRecType(self) if l in LabelsRecType(T)]
            OtherLabelsSelf = [l for l in LabelsRecType(self) if l not in LabelsRecType(T)]
            OtherLabelsT = [l for l in LabelsRecType(T) if l not in LabelsRecType(self)]
            for label in SharedLabels:
                T1 = AttValRecType(self,label)
                T2 = AttValRecType(T,label)
                if isinstance(T1, tuple) and isinstance(T2, tuple):
                    if T1[1] == T2[1]:
                        f1 = T1[0]
                        f2 = T2[0]
                        res.addfield(label, (merge_dep_types(f1,f2),T1[1]))
                    else:
                        f1 = T1[0]
                        f2 = T2[0]
                        res.addfield(label, (combine_dep_types(f1,f2),T1[1]+T2[1]))
                elif isinstance(T1,tuple) and isinstance(T2,TypeClass):
                    res.addfield(label, (combine_dep_types(T1[0],T2),T1[1]))
                elif isinstance(T1,TypeClass) and isinstance(T2,tuple):
                    res.addfield(label, (combine_dep_types(T1,T2[0]),T2[1]))
                else:
                    res.addfield(label, T1.merge(T2))
            for label in OtherLabelsSelf:
                res.addfield(label,AttValRecType(self,label))
            for label in OtherLabelsT:
                res.addfield(label,AttValRecType(T,label))
            return res
        elif self.subtype_of(T):
            return self
        else:
            from .compound_types import MeetType

            return MeetType(self,T)
    def amerge(self,T):
        if isinstance(T,RecType):
            res = RecType({})
            SharedLabels = [l for l in LabelsRecType(self) if l in LabelsRecType(T)]
            OtherLabelsSelf = [l for l in LabelsRecType(self) if l not in LabelsRecType(T)]
            OtherLabelsT = [l for l in LabelsRecType(T) if l not in LabelsRecType(self)]
            for label in SharedLabels:
                T1 = AttValRecType(self,label)
                T2 = AttValRecType(T,label)
                if isinstance(T1, tuple) and isinstance(T2, tuple):
                    if T1[1] == T2[1]:
                        f1 = T1[0]
                        f2 = T2[0]
                        if subtype_of_dep_types(f1,f2):
                            res.addfield(label, T1)
                        else:
                            res.addfield(label, T2)
                    else:
                        res.addfield(label, T2)
                elif isinstance(T1,tuple) and isinstance(T2,TypeClass):
                    res.addfield(label, T2)
                elif isinstance(T1,TypeClass) and isinstance(T2,tuple):
                    res.addfield(label,T2)
                elif isinstance(T1,TypeClass) and isinstance(T2,TypeClass):
                    if T1.subtype_of(T2):
                        res.addfield(label, T1)
                    else:
                        res.addfield(label, T1.amerge(T2))
                else:
                   res.addfield(label,T2) 
            for label in OtherLabelsSelf:
                res.addfield(label,AttValRecType(self,label))
            for label in OtherLabelsT:
                res.addfield(label,AttValRecType(T,label))
            return res
        elif self.subtype_of(T):
            return self
        else:
            return T

def LabelsRecType(T):
    if isinstance(T, RecType):
        return T.comps.labels()
    else:
        print('LabelsRecType not defined on '+ show(T) +' (not a record type)')
        return None

def AttValRecType(T,l):
    if isinstance(T, RecType):
        return T.comps[l]
    else:
        print('AttValRecType not defined on '+show(T)+' (not a record type)')
        return None

def RecOfRecType(r,T,M):
    TypeLabels = [l for l in T.comps]
    RecordLabels = [l for l in r]
    if forsome(TypeLabels, lambda l: l not in RecordLabels):
        return False
    elif forall(TypeLabels, lambda l: l in RecordLabels and QueryField(l,r,T,M)):
        return True
    else:
        return False

def QueryField(l,r,T,M):
    TInField = T.comps[l]
    Obj = r[l]
    if isinstance(Obj,HypObj):  # Should this be removed now?
        M = _M
    if isinstance(TInField, TypeClass):
        return TInField.in_poss(M).query(Obj) 
    else:
        TResolved = ComputeDepType(r,TInField,M)
        return TResolved.in_poss(M).query(Obj)

def ComputeDepType(r, DepType, M):
    if DepType[1] == []:
        #print(show(DepType[0]))
        return DepType[0]
    else:
        pth = DepType[1][0]
        if isinstance(pth,AbsPath):
            newfun = DepType[0].appc_m(pth.rec.pathvalue(pth.path), M)
        else:
            newfun = DepType[0].appc_m(r.pathvalue(DepType[1][0]), M)
        #print(show(newfun))
        return ComputeDepType(r, (newfun, DepType[1][1:]), M)

def CheckField(i,RecT):
    if isinstance(i[1], tuple): 
        return CheckPathList(i[1][1],RecT) 
    elif isinstance(i[1],RecType):
        return i[1].validate()
    else:
        return True

def CheckPathList(Paths, RecT):
    return forall(Paths, lambda x: CheckPath(x,RecT))

def CheckPath(path,RecT):
    if isinstance(path, AbsPath):
        return CheckPath(path.path,path.rec)
    else:
        res = RecT.pathvalue(path)
        if res is None:
            #print(res)
            return False
        else: return True

def ProcessDepFields(depfields,res,rtype,mode='real'):
    if len(depfields.comps) == 0:
        return res
    else:
        oldlength = len(depfields.comps)
        todelete = []
        for l in depfields.comps:
            Resolved = ComputeDepType(res,depfields.comps[l],rtype.poss)
            #print(show(Resolved))
            if 'not a label' in show(Resolved):  #Is this condition still used?
                pass
            elif Resolved is None:
                pass
            else:
                if mode=='real':
                    res.addfield(l,Resolved.in_poss(rtype.poss).create())
                    todelete.append(l)
                elif mode=='hyp':
                    res.addfield(l,Resolved.create_hypobj())
                    todelete.append(l)
                else:
                    print(mode+' not recognized as option for ProcessDepFields')
        for l in todelete:
            del depfields.comps[l]
        if len(depfields.comps) < oldlength:
            return ProcessDepFields(depfields,res,rtype,mode)
        else:
            if ttracing('create') or ttracing('create_hypobj'):
                print('Unresolved dependency in '+show(rtype))
            return None


__all__ = [
    "RecType",
    "LabelsRecType",
    "AttValRecType",
    "RecOfRecType",
    "QueryField",
    "ComputeDepType",
    "CheckField",
    "CheckPathList",
    "CheckPath",
    "ProcessDepFields",
]
