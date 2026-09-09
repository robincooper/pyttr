from collections import deque
from .utils import show, substitute, to_latex, trace, warn

_MISSING = object()

class Rec:
    def __init__(self,d=None):
        self.fields = {}
        if d is None:
            d = {}
        for item in d.items():
            if isinstance(item[1], dict):
                self.addfield(item[0], Rec(item[1]))
            else:
                self.addfield(item[0], item[1])

    def __getattr__(self, name):
        try:
            fields = object.__getattribute__(self, 'fields')
        except AttributeError:
            raise AttributeError(name) from None
        if name in fields:
            return fields[name]
        raise AttributeError(name)

    def __setattr__(self, name, value):
        if name == 'fields':
            object.__setattr__(self, name, value)
        else:
            try:
                fields = object.__getattribute__(self, 'fields')
            except AttributeError:
                object.__setattr__(self, name, value)
            else:
                fields[name] = value

    def __contains__(self, label):
        return label in self.fields

    def __getitem__(self, label):
        return self.fields[label]

    def __setitem__(self, label, value):
        self.fields[label] = value

    def __delitem__(self, label):
        del self.fields[label]

    def __iter__(self):
        return iter(self.fields)

    def __len__(self):
        return len(self.fields)

    def items(self):
        return self.fields.items()

    def keys(self):
        return self.fields.keys()

    def labels(self):
        return self.keys()

    def values(self):
        return self.fields.values()

    def get(self, label, default=None):
        return self.fields.get(label, default)

    def pop(self, label, default=_MISSING):
        if default is _MISSING:
            return self.fields.pop(label)
        return self.fields.pop(label, default)

    def as_dict(self):
        return dict(self.fields)
            
    def show(self):
        s = ""
        for kvp in self.fields.items():
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
        for kvp in self.fields.items():
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
        if label in self.fields:
            warn('"' + label + '"' + " is already a label in " + show(self))
        else: 
            self.fields[label] = value
            return self

    def addpath(self, path, value):
        pathl = path.split(".")
        return self.addpathl(pathl, value)

    def addpathl(self, pathl, value):
        if len(pathl) == 1:
            return self.addfield(pathl[0],value)
        elif pathl[0] in self.fields:
            val = self.fields[pathl[0]]
            if isinstance(val, Rec):
                val.addpathl(pathl[1:], value)
            else:
                warn(show(val) + ' is not a record.')
            return self
        else:
            self.addfield(pathl[0], Rec().addpathl(pathl[1:],value))
            return self
            
    def pathvalue(self, path):
        splits=deque(path.split("."))
        if (len(splits) == 1):
            if splits[0] in self.fields:
                return self.fields[splits[0]]
            else:
                trace('pathvalue', splits[0]+' not a label in '+self.show())
                return None
        else:
            addr = splits.popleft()
            if addr not in self.fields:
                trace('pathvalue', 'No attribute '+addr+' in '+show(self))
                return None
            elif not hasattr(self.fields[addr], 'pathvalue'):
                trace('pathvalue', 'No paths into '+show(self.fields[addr]))
                return None
            else:
                return self.fields[addr].pathvalue(".".join(splits))
    
    def relabel(self, oldlabel, newlabel):
        newrec = Rec(self.fields)
        if oldlabel in newrec.fields:
            value = newrec.fields.pop(oldlabel)
            newrec.fields[newlabel] = value
        return newrec
    
    def subst(self,v,a):
        res = Rec()
        for l in self.fields:
            lval = self.fields[l]
            if lval == v:
                res.addfield(l,a)
            elif isinstance(lval,str):
                res.addfield(l,lval)
            else: 
                res.addfield(l,substitute(lval,v,a))
        return res

    def eval(self):
        for l in self.fields:
            lval = self.fields[l]
            if hasattr(lval, 'eval'):
                self.fields[l] = lval.eval()
        return self
                
    def flatten(self):
        res = Rec()
        for l in self.fields:
            lval = self.fields[l]
            if isinstance(lval,str):
                res.addfield(l,lval)
            elif isinstance(lval,Rec):
                rec1 = lval.flatten()
                for l1 in rec1.fields:
                    res.addfield(l+"."+l1,rec1.fields[l1])
        return res

    def unflatten(self):
        res = Rec()
        for l in self.fields:
            res.addpath(l, self.fields[l])
        return res

    def addrec(self,r):
        res = Rec()
        for l in [l for l in self.fields if not l in r.fields]:
            res.addfield(l,self.fields[l])
        for l in [l for l in self.fields if l in r.fields]:
            rl = r.fields[l]
            sl = self.fields[l]
            if isinstance(rl, Rec) and isinstance(sl,Rec):
                res1 = sl.addrec(rl)
                if res1:
                    res.addfield(l,res1)
                else:
                    return None
            elif rl == sl:
                res.addfield(l,rl)
            else:
                return None
        for l in [l for l in r.fields if not l in self.fields]:
            res.addfield(l,r.fields[l])
        return res
 

    
