from ..core.model import _M
from ..core.records import Rec
from .type_core import TypeClass, logtype, logtype_t
from ..core.type_ops import equal
from ..utils import forall, gensym, show, substitute, to_latex

class TTRString(object):
    def __init__(self,list):
        self.items = list
    def concat(self,s):
        if isinstance(s, TTRString):
            return TTRString(self.items+s.items)
        else:
            return TTRString(self.items+[s])
    def startswith(self,T):
        firstT = next(filter(lambda x: T.query(x),[TTRString(self.items[0:i+1]) for i in range(len(self.items))]),None)
        if firstT:
            return TTRString(self.items[len(firstT.items):])
        else:
            return False

    def startswith_recursive(self,T):
        res = self.startswith(T)
        if res is False:
            return(res)
        elif res.items == []:
            return(True)
        else:
            return(res.startswith_recursive(T))
    def show(self):
        return '"'+' '.join([show(i) for i in self.items])+'"'
    def to_latex(self,vars):
        return '\\ '.join([to_latex(i,vars) for i in self.items])

class TTRStringType(TypeClass):
    def __init__(self,list_of_types):
        self.comps = Rec({'types' : list_of_types})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = \
          [lambda s: isinstance(s,TTRString) \
           and len(s.items) == len(self.comps.types) \
           and forall([x for x in range(len(self.comps.types))], \
                      lambda i: self.comps.types[i].in_poss(self.poss).query(s.items[i]))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '^'.join([show(i) for i in self.comps.types])
    def to_latex(self,vars):
        return '^\\frown'.join([to_latex(i,vars) for i in self.comps.types])
    def validate(self):
        return forall(self.comps.types, lambda T: isinstance(T,TypeClass))
    def learn_witness_condition(self,c):
        logtype(self,c)
        return None
    def learn_witness_type(self,c):
        logtype_t(self,c)
        return None
    def create(self):
        return TTRString([T.create() for T in self.comps.types])
    def create_hypobj(self):
        return TTRString([T.create_hypobj() for T in self.comps.types])
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return TTRStringType(substitute(self.comps.types,v,a))
    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        elif isinstance(T,TTRStringType) and len(T.comps.types)==len(self.comps.types):
            return TTRStringType([self.comps.types[i].merge(T.comps.types[i])
                                  for i in range(len(self.comps.types))])
        else:
            from .compound_types import MeetType

            return MeetType(self,T)
    def amerge(self,T):
        if self.subtype_of(T):
            return self
        elif isinstance(T,TTRStringType) and len(T.comps.types)==len(self.comps.types):
            return TTRStringType([self.comps.types[i].amerge(T.comps.types[i])
                                  for i in range(len(self.comps.types))])
        else:
            return T

class KPlusStringType(TypeClass):
    def __init__(self,strT):
        self.comps = Rec({'base_type' : strT})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = \
          [lambda s: isinstance(s,TTRString) and s.startswith_recursive(self.comps.base_type)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        if isinstance(self.comps.base_type, TTRStringType) and len(self.comps.base_type.comps.types)>1:
            return '('+show(self.comps.base_type)+')+'
        else:
            return show(self.comps.base_type)+'+'
    def to_latex(self,vars):
        if isinstance(self.comps.base_type, TTRStringType) and len(self.comps.base_type.comps.types)>1:
            return '('+to_latex(self.comps.base_type)+')^+'
        else:
            return to_latex(self.comps.base_type)+'^+'
    def validate(self):
        return isinstance(self.comps.base_type, TypeClass)
    def learn_witness_condition(self,c):
        logtype(self,c)
        return None
    def learn_witness_type(self,c):
        logtype_t(self,c)
        return None
    def create(self):
        a = gensym('_sigma')
        self.judge(a)
        return(a)
    def subtype_of(self,T):
        if T in self.supertype_cache: 
            return True
        elif equal(self,T):
            return True
        elif isinstance(T,KPlusStringType) and self.comps.base_type.subtype_of(T.comps.base_type):
            return True
        else:
            a = self.create_hypobj()
            if T.query(a):
                self.supertype_cache.append(T)
                return True
            else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return KPlusStringType(substitute(self.comps.base_type,v,a))
    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        elif isinstance(T,KPlusStringType):
            return KPlusStringType(self.comps.base_type.merge(T.comps.base_type))
        else:
            from .compound_types import MeetType

            return MeetType(self,T)

class KStarStringType(KPlusStringType):
    def __init__(self,strT):
        super().__init__(strT)
        self.witness_conditions = \
          [lambda s: isinstance(s,TTRString) and (s.items==[] or s.startswith_recursive(self.comps.base_type))]
    def to_latex(self,vars):
        if isinstance(self.comps.base_type, TTRStringType) and len(self.comps.base_type.comps.types)>1:
            return '('+to_latex(self.comps.base_type)+')^*'
        else:
            return to_latex(self.comps.base_type)+'^*'


__all__ = [
    "TTRString",
    "TTRStringType",
    "KPlusStringType",
    "KStarStringType",
]
