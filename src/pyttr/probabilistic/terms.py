from ..utils import show

from ..core.model import Possibility as CorePossibility
from ..core.terms import Fun as CoreFun

class Possibility(CorePossibility):
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(list(zip(self.model[i].witness_cache[0],self.model[i].witness_cache[1]))) for i in self.model])+'\n'+'_'*45+'\n'

    def _latex_entries(self):
        return (
            (key, list(zip(entry.witness_cache[0], entry.witness_cache[1])))
            for key, entry in self.model.items()
        )

class Fun(CoreFun):
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
