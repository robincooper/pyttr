from .records import Rec
from .type_core import TypeClass
from .utils import forall, gensym, show, substitute, to_latex, trace, warn

class Pred:
    def __init__(self,name,arity):
        self.name = name
        self.arity = arity
        self.witness_funs = []
    def show(self):
        return self.name
    def to_latex(self,vars):
        return to_latex(self.name.replace('_', '-'),vars)
    def learn_witness_fun(self,f):
        if f not in self.witness_funs:
            self.witness_funs.append(f)

class Fun(object):
    def __init__(self,v,dom,body):
        self.var = v
        self.domain_type = dom
        self.body = body
    def show(self):
        return 'lambda ' + self.var + ':' + self.domain_type.show() + ' . ' + show(self.body)
    def to_latex(self,vars):
        vars = vars+[self.var]
        return '\\lambda ' + to_latex(self.var,vars) + ':' + to_latex(self.domain_type,vars) + '\\ .\\ ' + to_latex(self.body,vars)
    def validate(self):
        if isinstance(self.var,str) and isinstance(self.domain_type,TypeClass):
            return True
        else: return False
    def validate_arg(self,arg):
        return self.domain_type.query(arg)
    def validate_arg_m(self,arg,M):
        return self.domain_type.in_poss(M).query(arg)
    def app(self,arg):
        if self.var == self.body: 
            return arg
        else: 
            res = substitute(self.body,self.var,arg)
            if hasattr(res, 'cache') and not isinstance(arg,HypObj):
                return res.cache()
            elif hasattr(res, 'eval'):
                return res.eval()
            else:
                return res
    def appc(self,arg):
        if self.validate_arg(arg):
            return self.app(arg)
        else:
            trace('appc', self.show()+'('+show(arg)+'): badly typed function application')
            return None
    def appc_m(self,arg,M):
        if self.validate_arg_m(arg,M):
            return self.app(arg)
        else:
            trace('appc_m', self.show()+'('+show(arg)+'): badly typed function application')
            return None            
                
    def subst(self,v,a):
        if self.var == v:
            return self  # v is bound and not replaced
        else: return Fun(self.var,substitute(self.domain_type,v,a),substitute(self.body,v,a))
    def in_poss(self,M):
        self.domain_type = self.domain_type.in_poss(M)
        return self

class HypObj(object):
    def __init__(self,types):
        self.types = types
        self.name = gensym('h')
    def validate(self):
        return forall(self.types,lambda x: isinstance(x,TypeClass))
    def show(self):
        return self.name
    def to_latex(self,vars):
        return self.name

class LazyObj(object):
    def __init__(self,strlist):
        self.oplist = strlist
    def subst(self,v,a):
        self.oplist = substitute(self.oplist,v,a)
        return self.eval()
    def eval(self):
        if isinstance(self.oplist[0],list) and\
                self.oplist[1] == '+' and\
                isinstance(self.oplist[2],list):
            return self.oplist[0] + self.oplist[2]
        elif isinstance(self.oplist[0],Fun) and\
                self.oplist[1] == '@':
            return self.oplist[0].app(self.oplist[2])
        elif isinstance(self.oplist[0],Rec) and\
                self.oplist[1] == '.':
            return getattr(self.oplist[0], self.oplist[2])
        elif isinstance(self.oplist[0],LazyObj):
            oldoplist = self.oplist
            self.oplist = [self.oplist[0].eval(),self.oplist[1],self.oplist[2]]
            if not oldoplist == self.oplist:
                return self.eval()
            else:
                return self
        else: return self
    def type(self):
        if self.oplist[1] == '@':
            if hasattr(self.oplist[0], 'types') and hasattr(self.oplist[2], 'types'):
                from .type_ops import ti_apply

                return ti_apply(self.oplist[0].types[0],
                                self.oplist[2].types[0])
            else:
                pass
        else:
            warn('Unable to compute type of ' + show(self))
            return None
    def show(self):
        return show(self.oplist)
    def to_latex(self,vars):
        return to_latex(self.oplist[0],vars)+to_latex(self.oplist[1],vars)+to_latex(self.oplist[2],vars)

class AbsPath(object):
    def __init__(self,rec,path):
        self.rec = rec
        self.path = path
    def show(self):
        return show(self.rec)+'.'+show(self.path)
    def to_latex(self,vars):
        return to_latex(self.rec,vars)+'.'+to_latex(self.path,vars)
    def subst(self,v,a):
        return AbsPath(substitute(self.rec,v,a),substitute(self.path,v,a))

class FunctionApplicationError(Exception):
    pass


__all__ = [
    "Pred",
    "Fun",
    "HypObj",
    "LazyObj",
    "AbsPath",
    "FunctionApplicationError",
]
