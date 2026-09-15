import numpy as np

from .. import config
from .constraints import ConjProb, PConstraint
from .type_core import QUERY_METHODS, TypeClass
from ..core.records import Rec
from ..core.record_types import RecTypeStructure, ComputeDepType
from ..core.type_ops import equal
from ..utils import forsome, show, trace

class RecType(RecTypeStructure, TypeClass):
    def __init__(self, d=None):
        super().__init__(d)
        self.witness_conditions = [lambda r, c, oracle: RecOfRecType(r, self, self.poss, c, oracle)]

    def in_poss(self, poss):
        self.poss = poss
        return self

    def create(self):
        return self._create_record()

    def create_hypobj(self):
        return self._create_record('hyp')

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
                if count == 0:
                    for r in vals:
                        chart[count].append(Rec({l:r}))
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
                for m in matches:
                    for s in m[0].in_poss(self.poss).sample(n):
                        r = Rec({l:s})
                        for p in T[1]:
                            newrec = Rec({})
                            newrec.addpath(p,m[1][T[1].index(p)])
                            r = r.addrec(newrec)
                        if count == 0:
                            chart[count].append(r)
                        else:
                            for rec in chart[count-1]:
                                combrec = rec.addrec(r)
                                if combrec:
                                        chart[count].append(combrec)
        count = count+1
        chart[count] = []
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
                       else:
                           for i in range(len(newrecs)):
                               m = np.random.choice(matches)
                               newrecs[i] = newrecs[i].addrec(Rec({l:m}))
                    for r in newrecs:
                        chart[count].append(rec.addrec(r))
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
            return ConjProb(list(map(lambda l: QueryField(l,r,T,M),TypeLabels)),c,oracle)

def QueryField(l,r,T,M):
    trace('QueryField', 'QueryField args: ', show([l,r,T,M]))
    TInField = T.comps[l]
    Obj = r[l]
    if isinstance(TInField, TypeClass):
        return (Obj,TInField.in_poss(M))
    else:
        TResolved = ComputeDepType(r,TInField,M)
        trace('TResolved', 'TResolved is: ', show((Obj,TResolved.in_poss(M))))
        return (Obj,TResolved.in_poss(M))


__all__ = [
    "RecType",
    "RecOfRecType",
    "QueryField",
]
