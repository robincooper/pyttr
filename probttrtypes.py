import inspect
import ttrtypes
from copy import deepcopy
from ttrtypes import HypObj, LazyObj, equal, Pred, add_to_model, _M
from utils import show, showall, forsome, gensym, check_stack, apply12


#----------------------------
# Type classes
#----------------------------

class TypeClass(ttrtypes.TypeClass):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
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
        
    def query(self, a,c=[],oracle=None):
        if not c:
            if a in self.witness_cache[0]:
                return self.witness_cache[1][self.witness_cache[0].index(a)]
            elif isinstance(a,HypObj) and show(self) in showall(a.types):
                return PConstraint(1)
            elif isinstance(a,HypObj) and forsome(a.types,
                                                  lambda T: show(self) in showall(T.supertype_cache)):
                return PConstraint(1)
            elif isinstance(a, LazyObj):
                if isinstance(a.eval(), LazyObj):
                    return a.eval().type().subtype_of(self)
                else:
                    return self.query(a.eval())
            elif self.witness_types:
                ps = list(map(lambda T: T.in_poss(self.poss).query(a), self.witness_types))
                res = PMax(ps)
                if not isinstance(a,HypObj):
                    self.witness_cache[0].append(a)
                    self.witness_cache[1].append(res)
                return res
            elif self.witness_conditions:
                ps = list(map(lambda c: apply12(c,a,oracle), self.witness_conditions))
                res = PMax(ps)
                if not isinstance(a,HypObj):
                    self.witness_cache[0].append(a)
                    self.witness_cache[1].append(res)
                return res
            else:
                return PConstraint(0,1)
        elif [i for i in filter(lambda x: isinstance(x,tuple),c)
              if i[0]==a and i[1].subtype_of(self)]:
            return PConstraint(1)
        elif oracle:
            res = oracle(a,self,c)
            if res:
                return res
            else:
                return self.query(a)
        else:
            return self.query(a)
    def forget(self,a):
        if a in self.witness_cache[0]:
            res = self.witness_cache[1].pop(self.witness_cache[0].index(a))
            self.witness_cache[0].remove(a)
            return res
    def query_nonspec(self,c=[],oracle=None):
        js = [(x,self) for x in self.witness_cache[0] if self.witness_cache[1][self.witness_cache[0].index(x)].max>0]
        p_nonspec = self.prob_nonspec
        if not c:
            if p_nonspec:
                if self.witness_cache[0]:
                    return PMax([p_nonspec,DisjProb(js,c,oracle)])
                else:
                    return p_nonspec
            else:
                if self.witness_cache[0]:
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
            if p_nonspec:
                if self.witness_cache[0]:
                    return PMax([p_nonspec,DisjProb(js,c,oracle)])
                else:
                    return p_nonspec
            else:
                if self.witness_cache[0]:
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
    def subtype_of(self,T):
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

def Type(name='',cs={},poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)



class BTypeClass(TypeClass):
    def __init__(self,name=gensym('BT')):
        ttrtypes.BTypeClass.__init__(self,name)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        
def BType(name=gensym('BT'),poss=_M):
    T = BTypeClass(name)
    return add_to_model(T,poss)



class PTypeClass(TypeClass):
    def __init__(self,pred,args):
        ttrtypes.PTypeClass.__init__(self,pred,args)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
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
    def query(self,a,c=[],oracle=None):
        # print(list(inspect.getargvalues(inspect.stack()[0][0]).locals.values()))
        # print(inspect.stack()[0][3])
        # print([a,c,oracle,self])
        # print(list(inspect.getargvalues(inspect.stack()[0][0]).locals.values())==[a,c,oracle,self])
        # print(check_stack('query',[a,c,oracle,self]))
        if check_stack('query',dict(a=a,c=c,oracle=oracle,self=self)):
            return PConstraint(0,1)
        elif not c:
            if a in self.witness_cache[0]:
               # print(show(self),show(a))
                return self.witness_cache[1][self.witness_cache[0].index(a)]
            elif isinstance(a,HypObj) and next(map(lambda T: equal(T,self), a.types),None):
                #show(self) in showall(a.types):
                return PConstraint(1)
            elif isinstance(a,HypObj) and next(map(lambda T: next(map(lambda T1: equal(T1,self),
                                                                      T.supertype_cache),None), a.types),None):
                #forsome(a.types, lambda T: show(self) in showall(T.supertype_cache)):
                return PConstraint(1)
            elif isinstance(a, LazyObj):
                if isinstance(a.eval(), LazyObj):
                    return a.eval().type().subtype_of(self)
                else:
                    return self.query(a.eval())
            elif self.witness_types:
                ps = list(map(lambda T: T.in_poss(self.poss).query(a), self.witness_types))
                res = PMax(ps)
                if not isinstance(a,HypObj):
                    self.witness_cache[0].append(a)
                    self.witness_cache[1].append(res)
            elif self.witness_conditions or self.comps.pred.witness_funs:
                condps = []
                for c in self.witness_conditions:
                    condps.append(c(a))
                for f in self.comps.pred.witness_funs:
                    type = f(self.comps.args).in_poss(self.poss)
                    if check_stack('query',[a,c,oracle,type]):
                        res = PConstraint(0,1)
                    else:
                        condps.append(type.query(a,c,oracle))
                        res = PMax(condps)
                # ps_witconds = list(map(lambda c: c(a), self.witness_conditions))
                # ps_witfuns = list(map(lambda f: f(self.comps.args).query(a,c,oracle), self.comps.pred.witness_funs))
                # res = PMax(ps_witconds+ps_witfuns)
                if not isinstance(a,HypObj):
                    self.witness_cache[0].append(a)
                    self.witness_cache[1].append(res)
                return res
            else:
                return PConstraint(0,1)
        elif [i for i in filter(lambda x: isinstance(x,tuple),c)
              if i[0]==a and i[1].subtype_of(self)]:
            return PConstraint(1)
        elif [i for i in filter(lambda x: isinstance(x,TypeClass),c)
              if i.subtype_of(self)]:
            return PConstraint(1)
        elif oracle:
            res = oracle(a,self,c)
            if res:
                return res
            else:
                return self.query(a)
        else:
            return self.query(a)
    

        #filter(lambda x: x[1].max>0,zip(self.witness_cache[0],self.witness_cache[1]))

def PType(pred,args,poss=_M):
    T = PTypeClass(pred,args)
    return add_to_model(T,poss)

class MeetType(TypeClass):
    def __init__(self,T1,T2):
        ttrtypes.MeetType.__init__(self,T1,T2)
        self.witness_cache = ([],[])
        self.prob_nonspec = None
        self.witness_conditions = [lambda a,oracle: ConjProb([(a,self.comps.left.in_poss(self.poss)),
                                                              (a,self.comps.right.in_poss(self.poss))],[],oracle)]
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

# class JoinType(TypeClass):
#     def __init__(self,T1,T2)
                                                            


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
    def to_latex(self,vars=[]):
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
    if len(jlist) == 0:
        return PConstraint(1)
    elif len(jlist) == 1:
        return jlist[0][1].query(jlist[0][0],c,oracle)
    else:
        j = jlist.pop()
        return PTimes(j[1].query(j[0],jlist+c,oracle),
                      ConjProb(jlist,c,oracle))
def DisjProb(jlist,c=[],oracle=None):
    if len(jlist) == 0:
        return PConstraint(0)
    elif len(jlist) == 1:
        return jlist[0][1].query(jlist[0][0],c,oracle)
    else:
        j = jlist.pop()
        return PMinus(PPlus(j[1].query(j[0]),DisjProb(jlist,c,oracle)),PTimes(j[1].query(j[0],jlist+c,oracle),
                      ConjProb(jlist,c,oracle)))
        
        


#------------------------------
# Non-type classes
#------------------------------

class Possibility(ttrtypes.Possibility):
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(list(zip(self.model[i].witness_cache[0],self.model[i].witness_cache[1]))) for i in self.model])+'\n'+'_'*45+'\n'
