from copy import copy, deepcopy

import numpy as np

from . import config, ttrtypes
from .prob_constraints import DisjProb, PConstraint, PExtreme, PMax
from .ttrtypes import HypObj, LazyObj, _M, add_to_model, equal
from .utils import apply123, check_stack, gensym, show, trace

QUERY_METHODS = [
    "_query_witness_cache",
    "_query_hypobj",
    "_query_lazyobj",
    "_query_conditions",
    "_query_oracle",
    "_query_witness_types",
    "_query_witness_conditions",
]

class TypeClass(ttrtypes.TypeClass):
    def __init__(self,name='',cs=None):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = QUERY_METHODS
    def in_poss(self,poss):
        key = self.show()
        if poss == '':
            return self
        elif key not in poss.model:
            poss.model[key] = deepcopy(self)
            poss.model[key].poss = poss
        else:
            old = poss.model[key]
            old.witness_cache[0].extend([x for x in self.witness_cache[0] if x not in old.witness_cache[0]])
            old.witness_cache[1].extend([x for x in self.witness_cache[1] if x not in old.witness_cache[1]])
            old.supertype_cache.extend([x for x in self.supertype_cache if x not in old.supertype_cache])
            old.witness_conditions.extend([x for x in self.witness_conditions if x not in old.witness_conditions])
            old.witness_types.extend([x for x in self.witness_types if x not in old.witness_types])
        return poss.model[key]
    def validate_witness(self, a, p):
        if self.witness_conditions == []:
            return True
        elif a in self.witness_cache[0] and isinstance(a,str):
            return True
        elif next((c for c in self.witness_conditions if p.match(c(a))),False):
            return True
        else:
            return False
    def judge(self, a, n=1, max=None):
        p = PConstraint(n,max)
        if a in self.witness_cache[0]:
           self.witness_cache[1][self.witness_cache[0].index(a)] = p
           return p
        elif isinstance(a,str):
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(p)
            return p
        elif self.validate_witness(a,p):
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(p)
            return p
        else: return False
    def judge_nonspec(self,n=1,max=None):
        self.prob_nonspec = PConstraint(n,max)
        return self.prob_nonspec

    def query(self, a,c=None,oracle=None):
        if c is None:
            c = []
        trace('query', 'query args: ', show([self,a,c,oracle]))
        if check_stack('query',dict(a=a,c=c,oracle=oracle,self=self)):
            return PConstraint(0,1)
        for m in self._query_methods:
            res = getattr(self, m)(a,c,oracle)
            if res and (res.min>0 or res.max<1):
                if not c:
                    if a in self.witness_cache[0]:
                        self.witness_cache[1][self.witness_cache[0].index(a)] = res
                    else:
                        if not isinstance(a,HypObj):
                            self.witness_cache[0].append(a)
                            self.witness_cache[1].append(res)
                return res
        if c or oracle:
            return self.query(a)
        else:
            return PConstraint(0,1)
    def _query_witness_cache(self,a,c,oracle):
        if not c and a in self.witness_cache[0]:
            return self.witness_cache[1][self.witness_cache[0].index(a)]
    def _query_hypobj(self,a,c,oracle):
        if isinstance(a,HypObj) and (next(filter(lambda T: equal(T,self), a.types),None) or
                                     next(filter(lambda T: next(filter(lambda T1: equal(T1,self),
                                                                 T.supertype_cache),None),
                                              a.types),None)):
            return PConstraint(1)
    def _query_lazyobj(self,a,c,oracle):
        if isinstance(a,LazyObj):
            if isinstance(a.eval(), LazyObj):
                return a.eval().type().subtype_of(self)
            else:
                return self.query(a.eval(),c,oracle)
    def _query_conditions(self,a,c,oracle):
        if [i for i in filter(lambda x: isinstance(x,tuple),c)
            if i[0]==a and i[1].subtype_of(self)]:
            return PConstraint(1)
    def _query_oracle(self,a,c,oracle):
        if oracle:
            return oracle(a,self,c)
    def _query_witness_types(self,a,c,oracle):
        if self.witness_types:
            ps = list(map(lambda T: T.in_poss(self.poss).query(a,c,oracle), self.witness_types))
            res = PMax(ps)
            return res
    def _query_witness_conditions(self,a,c,oracle):
        if self.witness_conditions:
            ps = list(map(lambda f: apply123(f,a,c,oracle), self.witness_conditions))
            res = PMax(ps)
            return res
    def forget(self,a):
        if a in self.witness_cache[0]:
            res = self.witness_cache[1].pop(self.witness_cache[0].index(a))
            self.witness_cache[0].remove(a)
            return res
    def query_nonspec(self,c=None,oracle=None):
        if c is None:
            c = []
        js = [(x,self) for x in self.sample()]
        for cond in c:
            if isinstance(cond,TypeClass):
                for x in cond.sample():
                    if (x,self) not in js:
                        js.append((x,self))
            elif isinstance(cond,tuple):
                for x in cond[1].sample():
                    if (x,self) not in js:
                        js.append((x,self))
        p_nonspec = self.prob_nonspec
        if not c:
            if p_nonspec:
                if self.witness_cache[0]:
                    return PMax([p_nonspec,DisjProb(js,c,oracle)])
                else:
                    return p_nonspec
            else:
                if js:
                    return DisjProb(js,c,oracle)
                else:
                    return PConstraint(0,1)
        elif [i for i in filter(lambda x: isinstance(x,tuple),c)
              if i[1].subtype_of(self)]:
            return PConstraint(1)
        elif [i for i in filter(lambda x: isinstance(x,TypeClass),c)
              if i.subtype_of(self)]:
            return PConstraint(1)
        elif oracle:
            oracle_nonspec = oracle(None,self,c)
            if p_nonspec:
                if oracle_nonspec:
                    return PMax([p_nonspec,oracle_nonspec])
                elif self.witness_cache[0]:
                    return PMax([p_nonspec,DisjProb(js,c,oracle)])
                else:
                    return p_nonspec
            else:
                if oracle_nonspec:
                    return oracle_nonspec
                elif self.witness_cache[0]:
                    return DisjProb(js,c,oracle)
                else:
                    return PConstraint(0,1)
        else:
            if p_nonspec:
                if self.witness_cache[0]:
                    return PMax([p_nonspec,DisjProb(js)])
                else:
                    return p_nonspec
            else:
                if self.witness_cache[0]:
                    return DisjProb(js)
                else:
                    return PConstraint(0,1)
    def query_doublecond(self,c:'python list of types',oracle=None):
        samples = self.sample()
        for T in c:
            for a in T.sample():
                if not a in samples:
                    samples.append(a)
        return PExtreme([self.query(a,[(a,T) for T in c],oracle) for a in samples])
    def subtype_of(self,T):
        trace('subtype_of', 'subtype_of args: ', show([self,T]))
        if T in self.supertype_cache: 
            return True
        elif equal(self,T):
            return True
        else:
            a = self.create_hypobj()
            if T.query(a).min == 1:
                self.supertype_cache.append(T)
                return True
            else: return False
    def sample(self,n=config.sample_size):
        wits = self.witness_cache[0]
        if len(wits)<=n:
            return copy(wits)
        else:
            return list(np.random.choice(wits,n,False))


def Type(name='',cs=None,poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)


class BTypeClass(TypeClass):
    def __init__(self,name=None):
        if name is None:
            name = gensym('BT')
        ttrtypes.BTypeClass.__init__(self,name)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = QUERY_METHODS


def BType(name=None,poss=_M):
    T = BTypeClass(name)
    return add_to_model(T,poss)


__all__ = [
    "TypeClass",
    "Type",
    "BTypeClass",
    "BType",
]
