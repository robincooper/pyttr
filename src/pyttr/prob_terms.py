from . import ttrtypes
from .utils import show

class Possibility(ttrtypes.Possibility):
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(list(zip(self.model[i].witness_cache[0],self.model[i].witness_cache[1]))) for i in self.model])+'\n'+'_'*45+'\n'

class Fun(ttrtypes.Fun):
    def matches(self,poss,n,vs=None,vartypes=None,varvalues=None):
        if vs is None:
            vs = []
        if vartypes is None:
            vartypes = []
        if varvalues is None:
            varvalues = []
        return self.body.matches(poss,n,vs+[self.var],vartypes+[self.domain_type],varvalues+[None])


__all__ = [
    "Possibility",
    "Fun",
]
