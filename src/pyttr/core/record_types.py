"""Record type structure and dependent-field traversal."""
from collections import deque
from .records import Rec
from .terms import AbsPath
from .type_core import TypeClass, logtype, logtype_t
from .type_ops import combine_dep_types, merge_dep_types, subtype_of_dep_types
from ..utils import (
    _show, _to_latex, forall, forsome, show, substitute, to_latex, trace,
    trace_any, warn,
)

class RecTypeStructure:
    def __init__(self, d=None):
        super().__init__()
        self.comps = Rec()
        for label, value in ({} if d is None else d).items():
            self.addfield(label, type(self)(value) if isinstance(value, dict) else value)

    def _create_record(self, mode='real'):
        res = Rec()
        depfields = type(self)()
        for label, field_type in self.comps.items():
            if isinstance(field_type, TypeClass):
                value = (field_type.in_poss(self.poss).create() if mode == 'real'
                         else field_type.create_hypobj())
                res.addfield(label, value)
            else:
                depfields.addfield(label, field_type)
        return ProcessDepFields(depfields, res, self, mode)

    def show(self, max_record_depth=None):
        return show(self, max_record_depth=max_record_depth)

    def _show(self, max_record_depth, record_depth):
        if max_record_depth is not None and record_depth >= max_record_depth:
            return "{...}"
        s = ""
        for kvp in self.comps.items():
            if s == "":
                s = s + kvp[0] + " : "
            else:
                s = s + ", "+kvp[0] + " : "
            
            s = s + _show(kvp[1], max_record_depth, record_depth + 1)
        return "{"+s+"}"

    def to_latex(self,vars=None,max_record_depth=None):
        return to_latex(self, vars=vars, max_record_depth=max_record_depth)

    def _to_latex(self,vars,max_record_depth,record_depth):
        if max_record_depth is not None and record_depth >= max_record_depth:
            return "\\left[\\cdots\\right]"
        s = ""
        for kvp in self.comps.items():
            if s == "":
                s = s + _to_latex(
                    kvp[0], [], None, None, max_record_depth, record_depth + 1
                ) + " &:& "
            else:
                s = s + "\\\\\n"+_to_latex(
                    kvp[0], [], None, None, max_record_depth, record_depth + 1
                ) + " &:& "
            s = s + _to_latex(
                kvp[1], vars, None, "yes", max_record_depth, record_depth + 1
            )
        return "\\left[\\begin{array}{lcl}\n"+s+"\n\\end{array}\\right]"

    def validate(self):
        if forall(list(self.comps.items()),lambda x: CheckField(x,self)) and self.create_hypobj() is not None:
            return True
        else:
            return False

    def addfield(self, label, value):
        if label in self.comps:
            warn('"' + label + '"' + " is already a label in this record type")
        else: 
            self.comps.addfield(label, value)

    def pathvalue(self, path):
        splits=deque(path.split("."))
        if (len(splits) == 1):
            if splits[0] in self.comps:
                return self.comps[splits[0]]
            else:
                trace('pathvalue', splits[0]+' not a label in '+self.show())
                return None
        else:
            addr = splits.popleft()
            if addr not in self.comps:
                trace('pathvalue', 'No attribute '+addr+' in '+show(self.comps))
                return None
            elif not hasattr(self.comps[addr], 'pathvalue'):
                trace('pathvalue', 'No paths into '+show(self.comps[addr]))
                return None
            else:
                return self.comps[addr].pathvalue(".".join(splits))

    def learn_witness_condition(self,c):
        logtype(self,c)

    def learn_witness_type(self,c):
        logtype_t(self,c)

    def Relabel(self, oldlabel, newlabel, recursive=False):
        if oldlabel in self.comps:
            value = self.comps.pop(oldlabel)
            self.comps[newlabel] = value
        return

    def subst(self,v,a):
        res = type(self)().in_poss(self.poss)
        for l in self.comps:
            lval = self.comps[l]
            if lval == v:
                res.addfield(l,a)
            elif isinstance(lval,str):
                res.addfield(l,lval)
            else: 
                res.addfield(l,substitute(lval,v,a))
        return res

    def eval(self):
        self.comps.eval()
        return self

    def merge(self,T):
        if isinstance(T, RecTypeStructure) and T._semantic_family != self._semantic_family:
            raise TypeError("Cannot merge record types from different semantics")
        if isinstance(T,RecTypeStructure):
            res = type(self)({}).in_poss(self.poss)
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
            return self._make_meet(T)

    def amerge(self,T):
        if isinstance(T, RecTypeStructure) and T._semantic_family != self._semantic_family:
            raise TypeError("Cannot merge record types from different semantics")
        if isinstance(T,RecTypeStructure):
            res = type(self)({}).in_poss(self.poss)
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
    if isinstance(T, RecTypeStructure):
        return T.comps.labels()
    else:
        raise TypeError('LabelsRecType is not defined on ' + show(T) + ' (not a record type)')

def AttValRecType(T,l):
    if isinstance(T, RecTypeStructure):
        return T.comps[l]
    else:
        raise TypeError('AttValRecType is not defined on ' + show(T) + ' (not a record type)')

def ComputeDepType(r, DepType, M):
    if DepType[1] == []:
        return DepType[0]
    else:
        pth = DepType[1][0]
        if isinstance(pth,AbsPath):
            newfun = DepType[0].appc_m(pth.rec.pathvalue(pth.path), M)
        else:
            newfun = DepType[0].appc_m(r.pathvalue(DepType[1][0]), M)
        return ComputeDepType(r, (newfun, DepType[1][1:]), M)

def CheckField(i,RecT):
    if isinstance(i[1], tuple): 
        return CheckPathList(i[1][1],RecT) 
    elif isinstance(i[1],RecTypeStructure):
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
            return False
        else: return True

def ProcessDepFields(depfields,res,rtype,mode='real'):
    if mode not in ('real', 'hyp'):
        raise ValueError(mode + ' not recognized as option for ProcessDepFields')
    if len(depfields.comps) == 0:
        return res
    else:
        oldlength = len(depfields.comps)
        todelete = []
        for l in depfields.comps:
            Resolved = ComputeDepType(res,depfields.comps[l],rtype.poss)
            if 'not a label' in show(Resolved):
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
        for l in todelete:
            del depfields.comps[l]
        if len(depfields.comps) < oldlength:
            return ProcessDepFields(depfields,res,rtype,mode)
        else:
            trace_any(('create', 'create_hypobj'), 'Unresolved dependency in '+show(rtype))
            return None
