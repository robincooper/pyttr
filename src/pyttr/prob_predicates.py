import numpy as np

from . import ttrtypes
from .prob_constraints import PConstraint, PMax
from .prob_type_core import QUERY_METHODS, TypeClass
from .ttrtypes import _M, Pred, add_to_model
from .utils import check_stack, substitute

class PTypeClass(TypeClass):
    def __init__(self,pred,args):
        ttrtypes.PTypeClass.__init__(self,pred,args)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = QUERY_METHODS
    show = ttrtypes.PTypeClass.show
    to_latex = ttrtypes.PTypeClass.to_latex
    def validate(self):
        if isinstance(self.comps.pred,Pred) \
                and len(self.comps.args) == len(self.comps.pred.arity):
            for i in zip(self.comps.args,self.comps.pred.arity):
                if i[1].query(i[0]).min == 1: pass
                else: return False
            return True
        else: return False
    create = ttrtypes.PTypeClass.create
    def subst(self,v,a):
        if self == v:
            return a
        else:
            newargs = []
            for arg in self.comps.args:
                if arg == v: newargs.append(a)
                elif isinstance(arg,str): newargs.append(arg)
                else: newargs.append(substitute(arg,v,a))      #arg.subst(v,a))
            return PType(self.comps.pred,newargs).in_poss(self.poss)
        #subst needs to be defined so that probttrtypes.PType is used rather than ttrtypes.PType (Bill Noble pull request, 7 Mar 2022)
    eval = ttrtypes.PTypeClass.eval
    def _query_witness_conditions(self,a,c,oracle):
        if self.witness_conditions or self.comps.pred.witness_funs:
            condps = []
            for cond in self.witness_conditions:
                condps.append(cond(a))
            for f in self.comps.pred.witness_funs:
                type = f(self.comps.args).in_poss(self.poss)
                # if check_stack('query',[a,c,oracle,type]):
                #     res = PConstraint(0,1)
                # else:
                #     condps.append(type.query(a,c,oracle))
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
