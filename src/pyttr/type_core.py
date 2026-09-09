from copy import copy

from .model import _M, add_to_model
from .records import Rec
from .utils import check_stack, forsome, gensym, show, showall, some_condition, to_latex, trace

class TypeClass:
    def __init__(self,name='',cs=None):
        if cs is None:
            cs = {}
        self.name = name
        if self.name == '': self.name = gensym('T')
        self.comps = Rec(cs)
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        key = self.show()
        if poss == _M:
            poss.model[key] = self
            return self
        elif key not in poss.model:
            new = copy(self)
            new.poss = poss
            new.witness_cache = copy(new.witness_cache)
            new.supertype_cache = copy(new.supertype_cache)
            new.witness_conditions = copy(new.witness_conditions)
            new.witness_types = copy(new.witness_types)
            poss.model[key] = new
            return new
        else:
            new = poss.model[key]
            new.witness_cache = new.witness_cache + [x for x in self.witness_cache if x not in new.witness_cache]
            new.supertype_cache = new.supertype_cache + [x for x in self.supertype_cache if x not in new.supertype_cache]
            new.witness_conditions = new.witness_conditions + [x for x in self.witness_conditions if x not in new.witness_conditions]
            new.witness_types = new.witness_types + [x for x in self.witness_types if x not in new.witness_types]
            return new
    
    def show(self):
        return self.name
    def to_latex(self,vars):
        return to_latex(self.name,vars,'italic')
    def learn_witness_condition(self, c):
        if c not in self.witness_conditions:
            self.witness_conditions.append(c)
    def learn_witness_type(self,T):
        if T not in self.witness_types:
            self.witness_types.append(T)
    def validate_witness(self, a):
        if self.witness_conditions == []:
            return True
        elif a in self.witness_cache and isinstance(a,str):
            return True
        else: return some_condition(self.witness_conditions,a)
    def judge(self, a):
        if a in self.witness_cache: return True
        elif isinstance(a,str):
            self.witness_cache.append(a)
            return True
        elif self.validate_witness(a):
            self.witness_cache.append(a)
            return True
        else: return False
    def judge_nonspec(self):
        if self.witness_cache == []:
            self.create()
        return True
    def query(self, a):
        from .terms import HypObj, LazyObj

        if check_stack('query', dict(a=a,self=self)):
             return '*'
        elif a in self.witness_cache: return True
        elif isinstance(a,HypObj) and show(self) in showall(a.types):
            return True
        elif isinstance(a,HypObj) and forsome(a.types,
                                              lambda T: show(self) in showall(T.supertype_cache)):
            return True
        elif isinstance(a, LazyObj):
            if isinstance(a.eval(), LazyObj):
                return a.eval().type().subtype_of(self)
            else:
                return self.query(a.eval())
        elif forsome(self.witness_types, lambda T: T.in_poss(self.poss).query(a)):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        else: 
            if some_condition(self.witness_conditions,a):
                if not isinstance(a,HypObj):
                    self.witness_cache.append(a)
                return True
            else:
                return False
        
    def query_nonspec(self):
        if self.witness_cache == []:
            return 'Don\'t know'
        else: return True
    def create(self):
        a = gensym('_a')
        self.judge(a)
        return a
    def create_hypobj(self):
        from .terms import HypObj

        return HypObj([self])
    def subtype_of(self,T):
        from .type_ops import equal

        if T in self.supertype_cache: 
            return True
        elif equal(self,T):
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
        else: return self
    def merge(self,T):
        from .compound_types import MeetType

        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        else:
            return MeetType(self,T)
    def amerge(self,T):
        if self.subtype_of(T):
            return self
        else:
            return T


def Type(name='',cs=None,poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)

class BTypeClass(TypeClass):
    def __init__(self,name=None):
        if name is None:
            name = gensym('BT')
        self.name=name
        self.comps = Rec({})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = _M

def BType(name=None,poss=_M):
    T = BTypeClass(name)
    return add_to_model(T,poss)


def logtype(x,c): 
    trace('learn_witness_condition', show(x)+' is a logical type and cannot learn new conditions')


def logtype_t(x,c): 
    trace('learn_witness_type', show(x)+' is a logical type and cannot learn new conditions')


__all__ = [
    "TypeClass",
    "Type",
    "BTypeClass",
    "BType",
    "logtype",
    "logtype_t",
]
