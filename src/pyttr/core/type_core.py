"""Shared type structure and semantic extension points."""
from abc import ABC, abstractmethod
from .records import Rec
from ..utils import gensym, show, to_latex, trace

class TypeClass(ABC):
    """Base for semantic implementations; query results are implementation-specific."""
    _semantic_family = None
    def __init__(self, name="", cs=None):
        self.name = name or gensym("T")
        self.comps = Rec({} if cs is None else cs)
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = self._default_poss

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

    def create_hypobj(self):
        from .terms import HypObj

        return HypObj([self])

    def subst(self,v,a):
        if self == v:
            return a
        else: return self

    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        else:
            return self._make_meet(T)

    def amerge(self,T):
        if self.subtype_of(T):
            return self
        else:
            return T

    @abstractmethod
    def judge(self, a):
        raise NotImplementedError("Semantic implementations define judge")

    @abstractmethod
    def query(self, a):
        raise NotImplementedError("Semantic implementations define query")

    @abstractmethod
    def create(self):
        raise NotImplementedError("Semantic implementations define create")

    @abstractmethod
    def in_poss(self, poss):
        raise NotImplementedError("Semantic implementations define in_poss")

    @abstractmethod
    def subtype_of(self, T):
        raise NotImplementedError("Semantic implementations define subtype_of")

    @abstractmethod
    def _make_meet(self, T):
        raise NotImplementedError("Semantic implementations define _make_meet")

    @abstractmethod
    def _query_succeeds(self, result):
        raise NotImplementedError("Semantic implementations define _query_succeeds")


def logtype(x,c): 
    trace('learn_witness_condition', show(x)+' is a logical type and cannot learn new conditions')

def logtype_t(x,c): 
    trace('learn_witness_type', show(x)+' is a logical type and cannot learn new conditions')

__all__ = ["TypeClass", "logtype", "logtype_t"]
