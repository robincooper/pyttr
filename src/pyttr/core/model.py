from ..utils import gensym, show, to_latex

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

    def _latex_entries(self):
        return (
            (key, entry.witness_cache)
            for key, entry in self.model.items()
            if key not in ('Ty', 'Re', 'RecTy')
        )

    def to_latex(self, vars=None):
        """Render the name and visible witness caches as a ruled LaTeX array."""
        rows = [
            to_latex(key, vars=vars) + ' & : & '
            + to_latex(witnesses, vars=vars)
            for key, witnesses in self._latex_entries()
        ]
        if not rows:
            rows = [' & & ']
        if self.name.startswith('_') or self.name.endswith('_'):
            name = r'\text{' + self.name.replace('_', r'\_') + '}'
        else:
            name = to_latex(self.name, vars=vars)
        heading = name + ': & & '
        return (
            '\\begin{array}{lcl}\n' + heading + '\\\\\n'
            + '\\hline\n' + '\\\\\n'.join(rows)
            + '\\\\\n\\hline\n\\end{array}'
        )

_M = Possibility('_Model_')
_default_models = [_M]

def register_default_model(model):
    _default_models.append(model)
    return model

def showmodel(m=_M):
    return show(m)

def initmodel():
    """Legacy reset: clear every loaded semantic default model."""
    for model in _default_models:
        model.model.clear()

def add_to_model(T,m=_M):
    key = T.show()
    if key in m.model:
        existing = m.model[key]
        if existing._semantic_family != T._semantic_family:
            raise TypeError("A model cannot intern different type implementations under " + key)
        return existing
    else:
        T.in_poss(m)
        return m.model[key] 


__all__ = [
    "Possibility",
    "_M",
    "showmodel",
    "initmodel",
    "add_to_model",
]
