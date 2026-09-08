import numpy as np

from . import config, ttrtypes
from .prob_constraints import ConjProb, PConstraint
from .prob_type_core import QUERY_METHODS, TypeClass
from .records import Rec
from .ttrtypes import ComputeDepType, equal
from .utils import forsome, show, ttracing

class RecType(TypeClass):
    def __init__(self,d=None):
        ttrtypes.RecType.__init__(self,d)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self.witness_conditions = [lambda r,c,oracle: RecOfRecType(r,self,self.poss,c,oracle)]
        self._query_methods = QUERY_METHODS
    in_poss = ttrtypes.RecType.in_poss
    show = ttrtypes.RecType.show
    to_latex = ttrtypes.RecType.to_latex
    validate = ttrtypes.RecType.validate
    addfield = ttrtypes.RecType.addfield
    pathvalue = ttrtypes.RecType.pathvalue
    learn_witness_condition = ttrtypes.RecType.learn_witness_condition
    learn_witness_type = ttrtypes.RecType.learn_witness_type
    create = ttrtypes.RecType.create
    create_hypobj = ttrtypes.RecType.create_hypobj
    Relabel = ttrtypes.RecType.Relabel
    subst = ttrtypes.RecType.subst
    eval = ttrtypes.RecType.eval
    merge = ttrtypes.RecType.merge
    amerge = ttrtypes.RecType.amerge
    def sample(self,n=config.sample_size):
        chart = {}
        count = -1
        nondepfields = RecType()
        for l in self.comps:
            T = self.comps[l]
            if isinstance(T,RecType):
                count = count+1
                chart[count] = []
                vals = T.in_poss(self.poss).sample(n)
                #print(show(T.in_poss(self.poss)))
                #print(vals)
                if count == 0:
                    for r in vals:
                        chart[count].append(Rec({l:r}))
                    #print(chart)
                else:
                    for r in vals:
                        for rec in chart[count-1]:
                            combrec = rec.addrec(Rec({l:r}))
                            if combrec:
                                chart[count].append(combrec)
                            else:
                                pass
            elif isinstance(T,TypeClass):
                nondepfields.addfield(l,T)
            else:
                count = count+1
                chart[count] = []
                matches = T[0].matches(self.poss,n)
                #print('matches: ', show(matches))
                for m in matches:
                    for s in m[0].in_poss(self.poss).sample(n):
                        r = Rec({l:s})
                        #print('r: ',show(r))
                        #print('T[1]',show(T[1]))
                        for p in T[1]:
                            newrec = Rec({})
                            newrec.addpath(p,m[1][T[1].index(p)])
                            #print('newrec:',show(newrec))
                            r = r.addrec(newrec)
                            #print('r after addrec: ',show(r))
                        if count == 0:
                            chart[count].append(r)
                        else:
                            for rec in chart[count-1]:
                                combrec = rec.addrec(r)
                                if combrec:
                                        chart[count].append(combrec)
        count = count+1
        chart[count] = []
        #print(show(nondepfields))
        if count == 0:
            newrecs = []
            for l in nondepfields.comps:
               matches = nondepfields.comps[l].in_poss(self.poss).sample(n)
               if newrecs == []:
                   for i in range(2*n):
                       m = np.random.choice(matches)
                       newrecs.append(Rec({l:m}))
               else:
                   for i in range(len(newrecs)):
                       m = np.random.choice(matches)
                       newrecs[i] = newrecs[i].addrec(Rec({l:m}))
            for r in newrecs:
                chart[count].append(r)
        else:
            for rec in chart[count-1]:
                if set([l for l in nondepfields.comps]).issubset(set([l for l in rec])):
                    chart[count].append(rec)
                else:
                    newrecs = []
                    for l in [l for l in nondepfields.comps if not l in rec]:
                       matches = nondepfields.comps[l].in_poss(self.poss).sample(n)
                       if newrecs == []:
                           for i in range(2*n):
                               m = np.random.choice(matches)
                               newrecs.append(Rec({l:m}))
                           # for m in matches:
                           #     newrecs.append(Rec({l:m}))
                       else:
                           for i in range(len(newrecs)):
                               m = np.random.choice(matches)
                               newrecs[i] = newrecs[i].addrec(Rec({l:m}))
                           # for r in newrecs:
                           #     m = np.random.choice(matches)
                           #     r.addrec(Rec({l:m}))
                    for r in newrecs:
                        chart[count].append(rec.addrec(r))
        #print(show(chart))
        res = []
        for r in chart[count]:
            if not any(map(lambda x: equal(x,r),res)):
                res.append(r)
        if len(res)<=n:
            return res
        else:
            return list(np.random.choice(res,n,False))


def RecOfRecType(r,T,M,c,oracle):
    if not isinstance(r,Rec):
        return PConstraint(0)
    else:
        TypeLabels = [l for l in T.comps]
        RecordLabels = [l for l in r]
        if forsome(TypeLabels, lambda l: l not in RecordLabels):
            return PConstraint(0)
        else:
            #print(show(list(map(lambda l: QueryField(l,r,T,M),TypeLabels))))
            return ConjProb(list(map(lambda l: QueryField(l,r,T,M),TypeLabels)),c,oracle)

def QueryField(l,r,T,M):
    if ttracing('QueryField'):
        print('QueryField args: ', show([l,r,T,M]))
    TInField = T.comps[l]
    Obj = r[l]
    # if isinstance(Obj,HypObj):
    #    M = _M
    if isinstance(TInField, TypeClass):
        return (Obj,TInField.in_poss(M))
        #print(show(TInField.in_poss(M).query(Obj))) 
    else:
        TResolved = ComputeDepType(r,TInField,M)
        if ttracing('TResolved'):
            print('TResolved is: ', show((Obj,TResolved.in_poss(M))))
        return (Obj,TResolved.in_poss(M))


__all__ = [
    "RecType",
    "RecOfRecType",
    "QueryField",
]
