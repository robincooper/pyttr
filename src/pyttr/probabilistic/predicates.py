import numpy as np

from .constraints import PConstraint, PMax
from .type_core import TypeClass
from .model import _M, add_to_model
from ..core.terms import Pred
from ..core.compound_types import PTypeClassStructure
from ..utils import check_stack

class PTypeClass(PTypeClassStructure, TypeClass):
    def __init__(self,pred,args):
        super().__init__(cs={"pred": pred, "args": args})
    def validate(self):
        if isinstance(self.comps.pred,Pred) \
                and len(self.comps.args) == len(self.comps.pred.arity):
            for i in zip(self.comps.args,self.comps.pred.arity):
                if i[1].query(i[0]).min == 1: pass
                else: return False
            return True
        else: return False
    def create(self):
        from ..utils import gensym
        a = gensym("_e")
        self.judge(a)
        return a

    def _query_witness_conditions(self,a,c,oracle):
        if self.witness_conditions or self.comps.pred.witness_funs:
            condps = []
            for cond in self.witness_conditions:
                condps.append(cond(a))
            for f in self.comps.pred.witness_funs:
                type = f(self.comps.args).in_poss(self.poss)
                if not check_stack('query',[a,c,oracle,type]):
                    condps.append(type.query(a,c,oracle))
            res = PMax(condps)
            return res
        else:
            return None
    def matches(self,poss,n,vs=None,vartypes=None,varvalues=None):
        if vs is None:
            vs = []
        if vartypes is None:
            vartypes = []
        if varvalues is None:
            varvalues = []
        pred = self.comps.pred
        args = self.comps.args
        res = []
        for T in poss.model.values():
            newvarvalues = varvalues.copy()
            if isinstance(T, PTypeClass):
                if pred in vs:
                    newvarvalues[vs.index(pred)] = T.comps.pred
                    matchlist(args,T.comps.args,poss,vs,vartypes,newvarvalues)
                    res.append((T,newvarvalues))
                elif pred == T.comps.pred:
                    matchlist(args,T.comps.args,poss,vs,vartypes,newvarvalues)
                    res.append((T,newvarvalues))
                else:
                    pass
        if len(res)<=n:
            return res
        else:
            return list(np.random.choice(res,n,False))


def matchlist(l1,l2,poss,vs=None,vartypes=None,varvalues=None):
    if vs is None:
        vs = []
    if vartypes is None:
        vartypes = []
    if varvalues is None:
        varvalues = []
    lgth = len(l1)
    if lgth == len(l2):
        for i in range(lgth):
            if l1[i] in vs and vartypes[vs.index(l1[i])].in_poss(poss).query(l2[i]).max>0:
                varvalues[vs.index(l1[i])] = l2[i]
                pass
            elif l1[i] == l2[i]:
                pass
            else:
                return False
    else:
        return False
    return True    


def PType(pred,args,poss=_M):
    T = PTypeClass(pred,args)
    return add_to_model(T,poss)


__all__ = [
    "PTypeClass",
    "PType",
    "matchlist",
]
