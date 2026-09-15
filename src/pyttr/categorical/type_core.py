from copy import copy

from ..core.model import _M, add_to_model
from ..core.records import Rec
from ..utils import check_stack, forsome, gensym, show, showall, some_condition, to_latex, trace

from ..core.type_core import TypeClass as CoreType

class TypeClass(CoreType):
    _default_poss = _M
    _semantic_family = 'categorical'

    def _make_meet(self, other):
        from .compound_types import MeetType
        return MeetType(self, other).in_poss(self.poss)

    def _query_succeeds(self, result):
        return bool(result)

    def __init__(self,name='',cs=None):
        super().__init__(name, cs)
        self.witness_cache = []
    def in_poss(self,poss):
        key = self.show()
        if key in poss.model and poss.model[key]._semantic_family != self._semantic_family:
            raise TypeError('A model cannot mix type implementations under ' + key)
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
    def subtype_of(self,T):
        from ..core.type_ops import equal

        if isinstance(T, CoreType) and self._semantic_family != T._semantic_family:
            return False
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


def Type(name='',cs=None,poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)

class BTypeClass(TypeClass):
    def __init__(self,name=None):
        if name is None:
            name = gensym('BT')
        super().__init__(name)

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
