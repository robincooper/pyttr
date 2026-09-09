from .utils import warn

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
            warn(str(n)+' is less than 0.')
            return False
        elif n>1:
            warn(str(n)+' is greater than 1.')
            return False
        elif m<0:
            warn(str(m)+' is less than 0.')
            return False
        elif m>1:
            warn(str(m)+' is greater than 1.')
            return False
        elif n>m:
            warn(str(n)+' is greater than '+str(m))
            return False
        else:
            return True
    def show(self):
        if self.max == self.min:
            return str(self.min)
        elif self.min>0 and self.max == 1:
            return '>='+str(self.min)
        elif self.min == 0:
            return '<='+str(self.max)
        else:
            return '>='+str(self.min)+'&<='+str(self.max)
    def to_latex(self,vs=None):
        if vs is None:
            vs = []
        if self.max == self.min:
            return str(self.min)
        elif self.min>0 and self.max == 1:
            return '\\geq'+str(self.min)
        elif self.min == 0:
            return '\\leq'+str(self.max)
        else:
            return '\\geq'+str(self.min)+'\\&\\leq'+str(self.max)
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
def PSum(plist):
    if plist:
        return PConstraint(sum(map(lambda p: p.min, plist)),
                          sum(map(lambda p: p.max, plist)))
def PNeg(p):
    return PConstraint(1-p.max,1-p.min)
def PRound(p,n=10):
    return PConstraint(round(p.min,n),round(p.max,n))
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
def ConjProb(jlist,c=None,oracle=None):
    if c is None:
        c = []
    if jlist:
        res = None
        for i in range(len(jlist)):
            j = jlist[i]
            if i:
                res = PTimes(res,j[1].query(j[0],jlist[:i]+c,oracle))
            else:
                res = j[1].query(j[0],c,oracle)
        return res
    else:
        return PConstraint(1)
def DisjProb(jlist,c=None,oracle=None):
    if c is None:
        c = []
    if jlist:
        res = None
        for i in range(len(jlist)):
            j = jlist[i]
            if i:
                res = PMinus(PPlus(res,j[1].query(j[0],c,oracle)),
                             PTimes(res,j[1].query(j[0],jlist[:i]+c,oracle)))
            else:
                res = j[1].query(j[0],c,oracle)
        return res
    else:
        return PConstraint(0)


__all__ = [
    "PConstraint",
    "PMax",
    "PExtreme",
    "PSum",
    "PNeg",
    "PRound",
    "PTimes",
    "PDiv",
    "PMinus",
    "PPlus",
    "ConjProb",
    "DisjProb",
]
