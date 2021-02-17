import ttrtypes
from copy import deepcopy
from ttrtypes import HypObj, LazyObj, equal, Pred
from utils import show, showall, forsome, gensym


#----------------------------
# Type classes
#----------------------------

class Type(ttrtypes.Type):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
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
                ps = list(map(lambda c: c(a), self.witness_conditions))
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
        if not c:
            return DisjProb(js,c,oracle)
        elif [i for i in filter(lambda x: isinstance(x,tuple),c)
              if i[1].subtype_of(self)]:
            return PConstraint(1)
        elif [i for i in filter(lambda x: isinstance(x,Type),c)
              if i.subtype_of(self)]:
            return PConstraint(1)
        elif oracle:
            return DisjProb(js,c,oracle)
        else:
            return DisjProb(js)
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

class BType(Type):
    def __init__(self,name=gensym('BT')):
        ttrtypes.BType.__init__(self,name)
        self.witness_cache = ([],[])

class PType(Type):
    def __init__(self,pred,args):
        ttrtypes.PType.__init__(self,pred,args)
        self.witness_cache = ([],[])
    show = ttrtypes.PType.show
    to_latex = ttrtypes.PType.to_latex
    def validate(self):
        if isinstance(self.comps.pred,Pred) \
                and len(self.comps.args) == len(self.comps.pred.arity):
            for i in zip(self.comps.args,self.comps.pred.arity):
                if i[1].query(i[0]).min == 1: pass
                else: return False
            return True
        else: return False
    create = ttrtypes.PType.create
    subst = ttrtypes.PType.subst
    eval = ttrtypes.PType.eval
    def query(self,a,c=[],oracle=None):
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
            elif self.witness_conditions or self.comps.pred.witness_funs:
                ps_witconds = list(map(lambda c: c(a), self.witness_conditions))
                ps_witfuns = list(map(lambda f: f(self.comps.args).in_poss(self.poss).query(a,c,oracle), self.comps.pred.witness_funs))
                res = PMax(ps_witconds+ps_witfuns)
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
    

        #filter(lambda x: x[1].max>0,zip(self.witness_cache[0],self.witness_cache[1]))

       


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
