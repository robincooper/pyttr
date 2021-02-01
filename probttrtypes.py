import ttrtypes
from ttrtypes import HypObj, LazyObj


#----------------------------
# Type classes
#----------------------------

class Type(ttrtypes.Type):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
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
    def query(self, a):
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
            ps = map(lambda T: T.in_poss(self.poss).query(a), self.witness_types)
            res = PMax(ps)
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(res)
        elif self.witness_conditions:
            ps = map(lambda c: c(a), self.witness_conditions)
            res = PMax(ps)
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(res)
            return res
        else:
            return PConstraint(0,1)


#--------------------
# Probability classes
#--------------------

class PConstraint:
    def __init__(self,n,m=None):
        if n<0:
            raise Exception(str(n)+' is less than 0.')
        if n>1:
            raise Exception(str(n)+' is greater than 1.')
        if m is None:
            pass
        elif m<0:
            raise Exception(str(m)+' is less than 0.')
        elif m>1:
            raise Exception(str(m)+' is greater than 1.')
        elif n>m:
            raise Exception(str(n)+' is greater than '+str(m))
                            
        self.min = float(n)
        if m is None:
            self.max = self.min
        else:
            self.max = m
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

def PMax(pmap):
    return PConstraint(max(map(lambda p: p.min, pmap)),
                       max(map(lambda p: p.max, pmap)))
