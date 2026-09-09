from .model import _M, add_to_model
from .records import Rec
from .terms import Fun, HypObj, LazyObj, Pred
from .type_core import TypeClass, logtype, logtype_t
from .type_ops import equal
from .utils import check_stack, forall, forsome, gensym, show, showall, some_condition, substitute, to_latex, trace

class PTypeClass(TypeClass):
    def __init__(self,pred,args): 
        self.comps = Rec({'pred':pred, 'args':args})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = _M
    def show(self):
        return self.comps.pred.name+'('+', '.join([show(x) for x in self.comps.args])+')'
    def to_latex(self,vars):
        return to_latex(self.comps.pred,vars)+'('+', '.join([to_latex(x,vars) for x in self.comps.args])+')'
    def validate(self):
        if isinstance(self.comps.pred,Pred) \
                and len(self.comps.args) == len(self.comps.pred.arity):
            for i in zip(self.comps.args,self.comps.pred.arity):
                if i[1].query(i[0]) == True: pass
                else: return False
            return True
        else: return False
    def create(self):
        e = gensym('_e')
        self.judge(e)
        return e
    def subst(self,v,a):
        if self == v:
            return a
        else:
            newargs = []
            for arg in self.comps.args:
                if arg == v: newargs.append(a)
                elif isinstance(arg,str): newargs.append(arg)
                else: newargs.append(substitute(arg,v,a))      #arg.subst(v,a))
            return PType(self.comps.pred,newargs).in_poss(self.poss)
    def eval(self):
        newargs = []
        for arg in self.comps.args:
            if hasattr(arg, 'eval'):
                newargs.append(arg.eval())
            else:
                newargs.append(arg)
        self.comps.args = newargs
        return self
    def query(self,a):
        if check_stack('query', dict(a=a,self=self)):
             return '*'
        elif a in self.witness_cache: return True
        elif isinstance(a,HypObj) and show(self) in showall(a.types):
            return True
        elif isinstance(a,HypObj) and forsome(a.types,
                                              lambda T: show(self) in showall(T.supertype_cache)):
            return True
        elif isinstance(a, LazyObj):
            if isinstance(a.eval(), LazyObj):
                return a.eval().type().subtype_of(self)
            else:
                return self.query(a.eval())
        elif forsome(self.witness_types, lambda T: T.in_poss(self.poss).query(a)):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        elif some_condition(self.witness_conditions,a):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        elif forsome(self.comps.pred.witness_funs, lambda f: f(self.comps.args).in_poss(self.poss).query(a)):
            if not isinstance(a, HypObj):
                self.witness_cache.append(a)
            return True
        else:
            return False

def PType(pred,args,poss=_M):
    T = PTypeClass(pred,args)
    return add_to_model(T,poss)

class MeetType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'left':T1, 'right':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a) \
                                       and self.comps.right.in_poss(self.poss).query(a)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
        
    def show(self):
        return '('+ self.comps.left.show()+'&'+self.comps.right.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ self.comps.left.to_latex(vars)+'\\wedge'+self.comps.right.to_latex(vars)+'\n\\end{array}\\right)'
    def learn_witness_condition(self,c):
        trace('learn_witness_condition', 'Meet types are logical and cannot learn new conditions')
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.left, TypeClass) \
                and isinstance(self.comps.right, TypeClass):
            return True
        else: return False
    def judge(self,a):
        if self.comps.left.judge(a) and self.comps.right.judge(a):
            return True
        else:
            return False
    def judge_nonspec(self):
        if self.witness_cache == [] and [x for x in self.comps.left.witness_cache if x in self.comps.right.witness_cache] == []:
            new = self.comps.left.create()
            self.comps.right.judge(new)
            self.judge(new)
        return True
    def create(self):
        a = self.comps.left.create()
        self.comps.right.judge(a)
        self.witness_cache.append(a)
        return a
    def create_hypobj(self):
        return HypObj([self.comps.left,self.comps.right,
                       self.comps.left.merge(self.comps.right)])
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return MeetType(self.comps.left.subst(v,a),self.comps.right.subst(v,a)).in_poss(self.poss)

class JoinType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'left':T1, 'right':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a), \
                                       lambda a: self.comps.right.in_poss(self.poss).query(a)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '('+ self.comps.left.show()+'v'+self.comps.right.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ self.comps.left.to_latex(vars)+'v'+self.comps.right.to_latex(vars)+'\n\\end{array}\\right)'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.left, TypeClass) \
                and isinstance(self.comps.right, TypeClass):
            return True
        else: return False
    def judge(self, a):
        if a in self.witness_cache: return True
        else:
            self.witness_cache.append(a)
            return True
    def subtype_of(self,T):
        if T in self.supertype_cache:
            return True
        elif equal(self,T):
            return True
        else:
            if self.comps.left.subtype_of(T) and self.comps.right.subtype_of(T):
                return True
            else:
                return False
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return JoinType(self.comps.left.subst(v,a),self.comps.right.subst(v,a))

class FunType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'domain':T1, 'range':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda f: isinstance(f,Fun) \
                                        and f.domain_type == self.comps.domain \
                                        and self.comps.range.query(f.app(self.comps.domain.create_hypobj()))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        return self
    def show(self):
        return '('+ self.comps.domain.show() + '->' + self.comps.range.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ to_latex(self.comps.domain,vars) + '->' + to_latex(self.comps.range,vars)+'\n\\end{array}\\right))'
    
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.domain, TypeClass) \
                and isinstance(self.comps.range, TypeClass):
            return True
        else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else: return FunType(self.comps.domain.subst(v,a),self.comps.range.subst(v,a))

class ListType(TypeClass):
    def __init__(self,T):
        self.comps = Rec({'base_type':T})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda l: isinstance(l,list) and forall(l, lambda x: T.in_poss(self.poss).query(x))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '['+ show(self.comps.base_type)+']'
    def to_latex(self,vars):
        return '\\left[\\begin{array}{rcl}\n'+ to_latex(self.comps.base_type,vars)+'\n\\end{array}\\right]'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.base_type,TypeClass):
            return True
        else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else: return ListType(substitute(self.comps.base_type,v,a))

class SingletonType(TypeClass):
    def __init__(self,T,a):
        self.comps = Rec({'base_type':T, 'obj':a})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda x: show(x) == show(a) and T.query(x),\
                                   lambda x: isinstance(a,LazyObj)\
                                             and show(x) == show(a.eval()) and T.in_poss(self.poss).query(x)]
        self.witness_types = []
        self.poss = _M 
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return show(self.comps.base_type)+'_'+ show(self.comps.obj)
    def to_latex(self,vars):
        return to_latex(self.comps.base_type,vars)+'_{'+ to_latex(self.comps.obj,vars)+'}'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.base_type,TypeClass):
            return True
        else: return False
    def create(self):
        self.judge(self.comps.obj)
        return self.comps.obj
    def create_hypobj(self):
        if hasattr(self.comps.obj, 'eval'):
            return self.comps.obj.eval()
        else:
            return self.comps.obj
    def subst(self,v,a):
        if self == v:
            return a
        else: return SingletonType(substitute(self.comps.base_type,v,a),substitute(self.comps.obj,v,a))


__all__ = [
    "PTypeClass",
    "PType",
    "MeetType",
    "JoinType",
    "FunType",
    "ListType",
    "SingletonType",
]
