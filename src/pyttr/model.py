from .utils import gensym, show

class Possibility:
    def __init__(self,name='',d=None):
        self.name = name
        if self.name == '': self.name = gensym('M')
        if d is None:
            self.model={}
        else:
            self.model = d
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(self.model[i].witness_cache) for i in self.model if i not in ['Ty','Re','RecTy']])+'\n'+'_'*45+'\n'

_M = Possibility('_Model_')

def showmodel(m=_M):
    return show(m)

def initmodel():
    global _M
    _M.model = {}

def add_to_model(T,m=_M):
    key = T.show()
    if key in m.model:
        return m.model[key]
    # elif 'validate' in dir(T) and T.validate():
    #     m.model[key] = deepcopy(T)
    #     m.model[key].poss = m
    #     return  m.model[key]
    else:
        # m.model[key] = copy(T)
        # m.model[key].poss = m
        T.in_poss(m)
        return m.model[key] 


__all__ = [
    "Possibility",
    "_M",
    "showmodel",
    "initmodel",
    "add_to_model",
]
