import numpy as np
import inspect
import config
import ttrtypes
from copy import deepcopy, copy
from ttrtypes import HypObj, LazyObj, equal, Pred, add_to_model, _M, ComputeDepType, Fun
from utils import show, showall, forsome, gensym, check_stack, apply123, ttracing
from records import Rec



#----------------------------
# Type classes
#----------------------------

class TypeClass(ttrtypes.TypeClass):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
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
        
    # def query(self, a,c=[],oracle=None):
    #     def setres(x):
    #         nonlocal res
    #         res = x
    #         return x
    #     if check_stack('query',dict(a=a,c=c,oracle=oracle,self=self)):
    #         return PConstraint(0,1)
    #     elif not c and a in self.witness_cache[0]:
    #             return self.witness_cache[1][self.witness_cache[0].index(a)]
    #     elif isinstance(a,HypObj) and show(self) in showall(a.types):
    #             return PConstraint(1)
    #     elif isinstance(a,HypObj) and forsome(a.types,
    #                                           lambda T: show(self) in showall(T.supertype_cache)):
    #         return PConstraint(1)
    #     elif isinstance(a, LazyObj):
    #         if isinstance(a.eval(), LazyObj):
    #             return a.eval().type().subtype_of(self)
    #         else:
    #             return self.query(a.eval(),c,oracle)
    #     elif [i for i in filter(lambda x: isinstance(x,tuple),c)
    #           if i[0]==a and i[1].subtype_of(self)]:
    #         return PConstraint(1)
    #     elif oracle and setres(oracle(a,self,c)):
    #         return res
    #        # res = oracle(a,self,c)
    #        # if res:
    #        #     return res
    #        # else:
    #        #     return self.query(a)
    #         #     pass
    #     elif self.witness_types:
    #         ps = list(map(lambda T: T.in_poss(self.poss).query(a,c,oracle), self.witness_types))
    #         res = PMax(ps)
    #         if not isinstance(a,HypObj):
    #             self.witness_cache[0].append(a)
    #             self.witness_cache[1].append(res)
    #         return res
    #     elif self.witness_conditions:
    #         ps = list(map(lambda f: apply123(f,a,c,oracle), self.witness_conditions))
    #         res = PMax(ps)
    #         if not isinstance(a,HypObj):
    #             self.witness_cache[0].append(a)
    #             self.witness_cache[1].append(res)
    #         if res.min == 0 and res.max == 1 and (c or oracle):
    #             return self.query(a)
    #         else:
    #             return res
    #         # else:
    #         #     return self.query(a)
    #     # else:
    #     #     return self.query(a)
    #     else:
    #         if c or oracle:
    #             return self.query(a)
    #         else:
    #             return PConstraint(0,1)
    def query(self, a,c=[],oracle=None):
        if ttracing('query'):
            print('query args: ',show([self,a,c,oracle]))
        if check_stack('query',dict(a=a,c=c,oracle=oracle,self=self)):
            return PConstraint(0,1)
        for m in self._query_methods:
            res = self.__getattribute__(m)(a,c,oracle)
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
            #print(show(self),show(self.witness_cache))
            return self.witness_cache[1][self.witness_cache[0].index(a)]
    def _query_hypobj(self,a,c,oracle):
        if isinstance(a,HypObj) and (next(map(lambda T: equal(T,self), a.types),None) or
                                     next(map(lambda T: next(map(lambda T1: equal(T1,self),
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
            # if res and (res.min>0 or res.max<1):
            #     return res
    def _query_witness_types(self,a,c,oracle):
        if self.witness_types:
            ps = list(map(lambda T: T.in_poss(self.poss).query(a,c,oracle), self.witness_types))
            res = PMax(ps)
            #if res and (res.min>0 or res.max<1):
                # if not isinstance(a,HypObj):
                #     self.witness_cache[0].append(a)
                #     self.witness_cache[1].append(res)
            return res
    def _query_witness_conditions(self,a,c,oracle):
        if self.witness_conditions:
            ps = list(map(lambda f: apply123(f,a,c,oracle), self.witness_conditions))
            res = PMax(ps)
            #if res and (res.min>0 or res.max>1):
                # if not isinstance(a,HypObj):
                #     self.witness_cache[0].append(a)
                #     self.witness_cache[1].append(res)
            return res
    def forget(self,a):
        if a in self.witness_cache[0]:
            res = self.witness_cache[1].pop(self.witness_cache[0].index(a))
            self.witness_cache[0].remove(a)
            return res
    def query_nonspec(self,c=[],oracle=None):
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
        #[(x,self) for x in self.witness_cache[0] if self.witness_cache[1][self.witness_cache[0].index(x)].max>0]
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
                    #print('js: ',show(js))
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
        if ttracing('subtype_of'):
            print('subtype_of args: ',show([self,T]))
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

def Type(name='',cs={},poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)



class BTypeClass(TypeClass):
    def __init__(self,name=gensym('BT')):
        ttrtypes.BTypeClass.__init__(self,name)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
        
def BType(name=gensym('BT'),poss=_M):
    T = BTypeClass(name)
    return add_to_model(T,poss)



class PTypeClass(TypeClass):
    def __init__(self,pred,args):
        ttrtypes.PTypeClass.__init__(self,pred,args)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
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
    subst = ttrtypes.PTypeClass.subst
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
    def matches(self,poss,n,vs=[],vartypes=[],varvalues=[]):
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

def matchlist(l1,l2,poss,vs=[],vartypes=[],varvalues=[]):
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
    
    
                    
    
    # def query(self,a,c=[],oracle=None):
    #     # print(list(inspect.getargvalues(inspect.stack()[0][0]).locals.values()))
    #     # print(inspect.stack()[0][3])
    #     # print([a,c,oracle,self])
    #     # print(list(inspect.getargvalues(inspect.stack()[0][0]).locals.values())==[a,c,oracle,self])
    #     # print(check_stack('query',[a,c,oracle,self]))
    #     if check_stack('query',dict(a=a,c=c,oracle=oracle,self=self)):
    #         return PConstraint(0,1)
    #     elif not c:
    #         if a in self.witness_cache[0]:
    #            # print(show(self),show(a))
    #             return self.witness_cache[1][self.witness_cache[0].index(a)]
    #         elif isinstance(a,HypObj) and next(map(lambda T: equal(T,self), a.types),None):
    #             #show(self) in showall(a.types):
    #             return PConstraint(1)
    #         elif isinstance(a,HypObj) and next(map(lambda T: next(map(lambda T1: equal(T1,self),
    #                                                                   T.supertype_cache),None), a.types),None):
    #             #forsome(a.types, lambda T: show(self) in showall(T.supertype_cache)):
    #             return PConstraint(1)
    #         elif isinstance(a, LazyObj):
    #             if isinstance(a.eval(), LazyObj):
    #                 return a.eval().type().subtype_of(self)
    #             else:
    #                 return self.query(a.eval())
    #         elif self.witness_types:
    #             ps = list(map(lambda T: T.in_poss(self.poss).query(a), self.witness_types))
    #             res = PMax(ps)
    #             if not isinstance(a,HypObj):
    #                 self.witness_cache[0].append(a)
    #                 self.witness_cache[1].append(res)
    #         elif self.witness_conditions or self.comps.pred.witness_funs:
    #             condps = []
    #             for c in self.witness_conditions:
    #                 condps.append(c(a))
    #             for f in self.comps.pred.witness_funs:
    #                 type = f(self.comps.args).in_poss(self.poss)
    #                 if check_stack('query',[a,c,oracle,type]):
    #                     res = PConstraint(0,1)
    #                 else:
    #                     condps.append(type.query(a,c,oracle))
    #                     res = PMax(condps)
    #             # ps_witconds = list(map(lambda c: c(a), self.witness_conditions))
    #             # ps_witfuns = list(map(lambda f: f(self.comps.args).query(a,c,oracle), self.comps.pred.witness_funs))
    #             # res = PMax(ps_witconds+ps_witfuns)
    #             if not isinstance(a,HypObj):
    #                 self.witness_cache[0].append(a)
    #                 self.witness_cache[1].append(res)
    #             return res
    #         else:
    #             return PConstraint(0,1)
    #     elif [i for i in filter(lambda x: isinstance(x,tuple),c)
    #           if i[0]==a and i[1].subtype_of(self)]:
    #         return PConstraint(1)
    #     elif [i for i in filter(lambda x: isinstance(x,TypeClass),c)
    #           if i.subtype_of(self)]:
    #         return PConstraint(1)
    #     elif oracle:
    #         res = oracle(a,self,c)
    #         if res:
    #             return res
    #         else:
    #             return self.query(a)
    #     else:
    #         return self.query(a)
    

        #filter(lambda x: x[1].max>0,zip(self.witness_cache[0],self.witness_cache[1]))

def PType(pred,args,poss=_M):
    T = PTypeClass(pred,args)
    return add_to_model(T,poss)

class MeetType(TypeClass):
    def __init__(self,T1,T2):
        ttrtypes.MeetType.__init__(self,T1,T2)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self.witness_conditions = [lambda a,c,oracle: ConjProb([(a,self.comps.left.in_poss(self.poss)),
                                                              (a,self.comps.right.in_poss(self.poss))],c,oracle)]
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
    in_poss = ttrtypes.MeetType.in_poss
    show = ttrtypes.MeetType.show
    to_latex = ttrtypes.MeetType.to_latex
    learn_witness_condition = ttrtypes.MeetType.learn_witness_condition
    learn_witness_type = ttrtypes.MeetType.learn_witness_type
    validate = ttrtypes.MeetType.validate
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
    create_hypobj = ttrtypes.MeetType.create_hypobj
    subst = ttrtypes.MeetType.subst

class JoinType(TypeClass):
    def __init__(self,T1,T2):
        ttrtypes.JoinType.__init__(self,T1,T2)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self.witness_conditions = [lambda a,c,oracle: DisjProb([(a,self.comps.left.in_poss(self.poss)),
                                                              (a,self.comps.right.in_poss(self.poss))],c,oracle)]
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
    in_poss = ttrtypes.JoinType.in_poss
    show = ttrtypes.JoinType.show
    to_latex = ttrtypes.JoinType.to_latex
    learn_witness_condition = ttrtypes.JoinType.learn_witness_condition
    learn_witness_type = ttrtypes.JoinType.learn_witness_type
    validate = ttrtypes.JoinType.validate
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
    subtype_of = ttrtypes.JoinType.subtype_of
    subst = ttrtypes.JoinType.subst

# FunType to be implemented

# ListType to be implemented

# SingletonType to be implemented

class RecType(TypeClass):
    def __init__(self,d={}):
        ttrtypes.RecType.__init__(self,d)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self.witness_conditions = [lambda r,c,oracle: RecOfRecType(r,self,self.poss,c,oracle)]
        self._query_methods = ['_query_witness_cache','_query_hypobj','_query_lazyobj','_query_conditions','_query_oracle','_query_witness_types','_query_witness_conditions']
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
        for l in self.comps.__dict__:
            T = self.comps.__getattribute__(l)
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
            for l in nondepfields.comps.__dict__:
               matches = nondepfields.comps.__getattribute__(l).in_poss(self.poss).sample(n)
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
                #print([l for l in rec.__dict__],[l for l in nondepfields.comps.__dict__]) 
                if set([l for l in nondepfields.comps.__dict__]).issubset(set([l for l in rec.__dict__])):
                    chart[count].append(rec)
                else:
                    newrecs = []
                    for l in [l for l in nondepfields.comps.__dict__ if not l in rec.__dict__]:
                       matches = nondepfields.comps.__getattribute__(l).in_poss(self.poss).sample(n)
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
        #return chart[count]
    
        
                
              
                    
                    
                
                
                    
    
    # def query_nonspec(self,c=[],oracle=None):
    #     TypeLabels = [l for l in self.comps.__dict__]
    #     return ConjProb(list(map(lambda l: QueryField_nonspec(l,self,self.poss),TypeLabels)),c,oracle)

def RecOfRecType(r,T,M,c,oracle):
    if not isinstance(r,Rec):
        return PConstraint(0)
    else:
        TypeLabels = [l for l in T.comps.__dict__]
        RecordLabels = [l for l in r.__dict__]
        if forsome(TypeLabels, lambda l: l not in RecordLabels):
            return PConstraint(0)
        else:
            #print(show(ConjProb(list(map(lambda l: QueryField(l,r,T,M),TypeLabels)),c,oracle)))
            return ConjProb(list(map(lambda l: QueryField(l,r,T,M),TypeLabels)),c,oracle)
        # elif forall(TypeLabels, lambda l: l in RecordLabels and QueryField(l,r,T,M)):
        #     return True
        # else:
        #     return False
def QueryField(l,r,T,M):
    if ttracing('QueryField'):
        print('QueryField args: ', show([l,r,T,M]))
    TInField = T.comps.__getattribute__(l)
    Obj = r.__getattribute__(l)
    # if isinstance(Obj,HypObj):
    #     M = _M
    if isinstance(TInField, TypeClass):
        return (Obj,TInField.in_poss(M))
    #TInField.in_poss(M).query(Obj) 
    else:
        TResolved = ComputeDepType(r,TInField,M)
        if ttracing('TResolved'):
            print('TResolved is: ', show((Obj,TResolved.in_poss(M))))
        return (Obj,TResolved.in_poss(M))
    #TResolved.in_poss(M).query(Obj)

# def QueryField_nonspec(l,T,M):
#     if ttracing('QueryField'):
#         print('QueryField args: ', show([l,T,M]))
#     TInField = T.comps.__getattribute__(l)
#     if isinstance(TInField, TypeClass):
#         return TInField.in_poss(M).query_nonspec()
#     #TInField.in_poss(M).query(Obj) 
#     else:
#         TResolved = ComputeDepType(r,TInField,M)
#         if ttracing('TResolved'):
#             print('TResolved is: ', show((Obj,TResolved.in_poss(M))))
#         return (Obj,TResolved.in_poss(M))
#     #TResolved.in_poss(M).query(Obj)
#--------------------
# Probability classes
#--------------------

class PConstraint:
    def __init__(self,n,m=None):
        
                            
        self.min = float(n)
        if m is None:
            self.max = self.min
        else:
            self.max = float(m)
    def validate(self):
        n = self.min
        m = self.max
        if n<0:
            print(str(n)+' is less than 0.')
            return False
        elif n>1:
            print(str(n)+' is greater than 1.')
            return False
        elif m:
            if m<0:
                print(str(m)+' is less than 0.')
                return False
            elif m>1:
                print(str(m)+' is greater than 1.')
                return False
            elif n>m:
                print(str(n)+' is greater than '+str(m))
                return False
        else:
            return True
    def show(self):
        if self.max == self.min:
            return str(self.min)
        # elif self.min == 0 and self.max == 1:
        #     return 'no constraint'
        elif self.min>0 and self.max == 1:
            return '>='+str(self.min)
        elif self.min == 0:
            return '<='+str(self.max)
        else:
            return '>='+str(self.min)+'&<='+str(self.max)
    def to_latex(self,vs=[]):
        if self.max == self.min:
            return str(self.min)
        # elif self.min == 0 and self.max == 1:
        #     return '\mathrm{no\ constraint}'
        elif self.min>0 and self.max == 1:
            return '\geq'+str(self.min)
        elif self.min == 0:
            return '\leq'+str(self.max)
        else:
            return '\geq'+str(self.min)+'\&\leq'+str(self.max)
    def match(self,p):
        return p.min<=self.min and self.max<=p.max

        
  
#---------------------
# Probability functions
#---------------------

def PMax(plist):
    return PConstraint(max(map(lambda p: p.min, plist)),
                       max(map(lambda p: p.max, plist)))
def PExtreme(plist):
    if plist:
        return PConstraint(min(map(lambda p: p.min, plist)),
                           max(map(lambda p: p.max, plist)))
def PNeg(p):
    return PConstraint(1-p.max,1-p.min)
def PTimes(p1,p2):
    return PConstraint(p1.min*p2.min,p1.max*p2.max)
def PDiv(p1,p2):
    if p2.min>0:
        min=p1.min/p2.min
    else:
        min=0
    if p2.max>0:
        max=p1.max/p2.max
    else:
        max=0
    return PConstraint(min,max)
def PMinus(p1,p2):
    return PConstraint(p1.min-p2.min,p1.max-p2.max)
def PPlus(p1,p2):
    return PConstraint(p1.min+p2.min,p1.max+p2.max)
def ConjProb(jlist,c=[],oracle=None):
    if jlist:
        res = None
        for i in range(len(jlist)):
            j = jlist[i]
            if i:
                res = PTimes(res,j[1].query(j[0],jlist[:i]+c,oracle))
            else:
                res = j[1].query(j[0],c,oracle)
            #print('conjres: ',show(res))
        return res
    else:
        return PConstraint(1)
                
    # print(show(jlist))
    # print(show(c))
    # if ttracing('ConjProb'):
    #     print('ConjProb args: ',show([jlist,c,oracle]))
    # if len(jlist) == 0:
    #     return PConstraint(1)
    # elif len(jlist) == 1:
    #     return jlist[0][1].query(jlist[0][0],c,oracle)
    # else:
    #     j = jlist[-1]
    #     if ttracing('ConjProb'):
    #         print('ConjProb result: ', show(PTimes(j[1].query(j[0],jlist[:-1]+c,oracle),
    #                   ConjProb(jlist[:-1],c,oracle))))
    #     return PTimes(j[1].query(j[0],jlist[:-1]+c,oracle),
    #                   ConjProb(jlist[:-1],c,oracle))
def DisjProb(jlist,c=[],oracle=None):
    if jlist:
        res = None
        for i in range(len(jlist)):
            #print(i)
            j = jlist[i]
            if i:
                res = PMinus(PPlus(res,j[1].query(j[0],c,oracle)),
                             PTimes(res,j[1].query(j[0],jlist[:i]+c,oracle)))
            else:
                res = j[1].query(j[0],c,oracle)
            #print('res: ',show(res))
        return res
    else:
        return PConstraint(0)
        
    # if ttracing('DisjProb'):
    #     print('DisjProb args: ',show([jlist,c,oracle]))
    # if len(jlist) == 0:
    #     return PConstraint(0)
    # elif len(jlist) == 1:
    #     return jlist[0][1].query(jlist[0][0],c,oracle)
    # else:
    #     j = jlist[-1]
    #     if ttracing('DisjProb'):
    #         print('j: ', show(j))
    #         print('jlist+c: ',show(jlist[:-1]+c))
    #         print('result: ', show(PMinus(PPlus(j[1].query(j[0],c,oracle),DisjProb(jlist[:-1],c,oracle)),PTimes(j[1].query(j[0],jlist[:-1]+c,oracle),
    #                   ConjProb(jlist[:-1],c,oracle)))))
    #     return PMinus(PPlus(j[1].query(j[0],c,oracle),DisjProb(jlist[:-1],c,oracle)),PTimes(j[1].query(j[0],jlist[:-1]+c,oracle),
    #                   ConjProb(jlist[:-1],c,oracle)))
        
        


#------------------------------
# Non-type classes
#------------------------------

class Possibility(ttrtypes.Possibility):
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(list(zip(self.model[i].witness_cache[0],self.model[i].witness_cache[1]))) for i in self.model])+'\n'+'_'*45+'\n'

class Fun(ttrtypes.Fun):
    def matches(self,poss,n,vs=[],vartypes=[],varvalues=[]):
        return self.body.matches(poss,n,vs+[self.var],vartypes+[self.domain_type],varvalues+[None])
