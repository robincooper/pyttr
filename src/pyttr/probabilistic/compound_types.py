from .constraints import ConjProb, DisjProb, PConstraint, PDiv, PNeg, PSum
from .type_core import QUERY_METHODS, TypeClass
from ..core.records import Rec
from ..core.type_core import logtype, logtype_t
from ..core.compound_types import MeetTypeStructure, JoinTypeStructure
from ..utils import show, trace

class MeetType(MeetTypeStructure, TypeClass):
    def in_poss(self, poss):
        self.poss = poss
        return self

    def create_hypobj(self):
        from ..core.terms import HypObj
        return HypObj([self.comps.left, self.comps.right, self.comps.left.merge(self.comps.right)])

    def __init__(self,T1,T2):
        super().__init__(cs={"left": T1, "right": T2})
        self.witness_conditions = [lambda a,c,oracle: ConjProb([(a,self.comps.left.in_poss(self.poss)),
                                                              (a,self.comps.right.in_poss(self.poss))],c,oracle)]
        self._query_methods = QUERY_METHODS
    def judge(self,a,n=1,max=None):
        p = PConstraint(n,max)
        if p.min == p.max == 1:
            self.comps.left.in_poss(self.poss).judge(a)
            self.comps.right.in_poss(self.poss).judge(a)
        return super().judge(a,n,max)
    def judge_nonspec(self,n=1,max=None):
        p = PConstraint(n,max)
        if p.min == p.max == 1:
            self.comps.left.in_poss(self.poss).judge_nonspec()
            self.comps.right.in_poss(self.poss).judge_nonspec()
        return super().judge_nonspec(n,max)
    def create(self):
        a = self.comps.left.create()
        self.comps.right.judge(a)
        self.witness_cache[0].append(a)
        self.witness_cache[1].append(PConstraint(1))
        return a

class JoinType(JoinTypeStructure, TypeClass):
    def in_poss(self, poss):
        self.poss = poss
        return self

    def subtype_of(self, T):
        from ..core.type_ops import equal
        if T in self.supertype_cache or equal(self, T):
            return True
        return self.comps.left.subtype_of(T) and self.comps.right.subtype_of(T)

    def __init__(self,T1,T2):
        super().__init__(cs={"left": T1, "right": T2})
        self.witness_conditions = [lambda a,c,oracle: DisjProb([(a,self.comps.left.in_poss(self.poss)),
                                                              (a,self.comps.right.in_poss(self.poss))],c,oracle)]
        self._query_methods = QUERY_METHODS
    def judge(self,a,n=1,max=None):
        p = PConstraint(n,max)
        if p.min == p.max == 0:
            self.comps.left.in_poss(self.poss).judge(a,0)
            self.comps.right.in_poss(self.poss).judge(a,0)
        return super().judge(a,n,max)
    def judge_nonspec(self,n=1,max=None):
        p = PConstraint(n,max)
        if p.min == p.max == 0:
            self.comps.left.in_poss(self.poss).judge_nonspec(0)
            self.comps.right.in_poss(self.poss).judge_nonspec(0)
        return super().judge_nonspec(n,max)

# FunType to be implemented

# ListType to be implemented

# SingletonType to be implemented

class NegType(TypeClass):
    def __init__(self,T):
        super().__init__(cs={'base_type':T})
        self.witness_conditions = [lambda a,c,oracle: PNeg(self.comps.base_type.query(a,c,oracle))]
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def judge(self,a,n=1,max=None):
        return self.comps.base_type.judge(a,1-max,1-n)
    def judge_nonspec(self,n=1,max=None):
        return self.comps.base_type.judge_nonspec(1-max,1-n)
    def query(self,a,c=None,oracle=None):
        if c is None:
            c = []
        return PNeg(self.comps.base_type.query(a,c,oracle))
    def query_nonspec(self,c=None,oracle=None):
        if c is None:
            c = []
        return PNeg(self.comps.base_type.query_nonspec(c,oracle))
    def query_doublecond(self,c:'python list of types',oracle=None):
        return PNeg(self.comps.base_type.query_doublecond(c,oracle))

class VarType(TypeClass):
    def __init__(self,types:'list of types',name=''):
        super().__init__(name,{'value_types':types})
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def judge(self,a,n=1,max=None):
        trace('judge', show(self)+' is a variable type and cannot be judged')
    def judge_nonspec(self,n=1,max=None):
        trace('judge_nonspec', show(self)+' is a variable type and cannot be judged')
    def query(self,a,c=None,oracle=None):
        if c is None:
            c = []
        Ts = [A for (a,A) in c if [B for B in self.comps.value_types if A.subtype_of(B)]]
        if len(Ts) == 1:
            return PConstraint(1)
        elif len(Ts)>1:
            return PConstraint(0)
        else:
            return PSum([self.query_v(a,T,c,oracle) for T in self.comps.value_types])
    def query_normal(self,a):
        sum = PSum([T.query(a) for T in self.comps.value_types])
        if sum.min == 1 and sum.max == 1:
            return True
        else:
            return False
    def query_v(self,a,T,c=None,oracle=None):
        if c is None:
            c = []
        Ts = [A for (a,A) in c if [B for B in self.comps.value_types if A.subtype_of(B)]]
        if len(Ts) == 1 and T.subtype_of(Ts[0]):
            return PConstraint(1)
        elif len(Ts)>1:
            return None
        elif [A for A in self.comps.value_types if T.subtype_of(A)] and [A for A in Ts if not T.subtype_of(A)]:
            return PConstraint(0)
        elif len([A for A in self.comps.value_types if T.subtype_of(A)])>1:
            return PConstraint(0)
        else:
            denominator = PSum([A.query(a,c,oracle) for A in self.comps.value_types])
            return PDiv(T.query(a,c,oracle),denominator)
    def query_nonspec(self,c=None,oracle=None):
        if c is None:
            c = []
        return PSum([self.query_nonspec_v(T,c,oracle) for T in self.comps.value_types])
    def query_nonspec_v(self,T,c=None,oracle=None):
        if c is None:
            c = []
        if T in self.comps.value_types:
            denominator = PSum([A.query_nonspec(c,oracle) for A in self.comps.value_types])
            return PDiv(T.query_nonspec(c,oracle),denominator)
        else:
           supertypes = map(lambda T1 : T.subtype_of(T1), self.comps.value_types) 
           if any(supertypes)  and any(supertypes):
               return PConstraint(0)
           else:
               return PConstraint(0,1)
    def query_doublecond(self,c:'python list of types',oracle=None):
        return PSum([self.query_doublecond_v(T,c,oracle) for T in self.comps.value_types])
    def query_doublecond_v(self,T,c=None,oracle=None):
        if c is None:
            c = []
        if T in self.comps.value_types:
            denominator = PSum([A.query_doublecond(c,oracle) for A in self.comps.value_types])
            return PDiv(T.query_doublecond(c,oracle),denominator)
        else:
           supertypes = map(lambda T1 : T.subtype_of(T1), self.comps.value_types) 
           if any(supertypes)  and any(supertypes):
               return PConstraint(0)
           else:
               return PConstraint(0,1)


__all__ = [
    "MeetType",
    "JoinType",
    "NegType",
    "VarType",
]
