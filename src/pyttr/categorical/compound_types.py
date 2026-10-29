from ..core.compound_types import PTypeClassStructure, MeetTypeStructure, JoinTypeStructure, FunTypeStructure, ListTypeStructure, SingletonTypeStructure
from ..core.model import _M, add_to_model
from ..core.records import Rec
from .terms import Fun, HypObj, LazyObj, Pred
from .type_core import TypeClass, logtype, logtype_t
from ..core.type_ops import equal
from ..utils import check_stack, forall, forsome, gensym, show, showall, some_condition, substitute, to_latex, trace

class PTypeClass(PTypeClassStructure, TypeClass):
    def __init__(self,pred,args): 
        super().__init__(cs={'pred':pred, 'args':args})
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

class MeetType(MeetTypeStructure, TypeClass):
    def __init__(self,T1,T2): 
        super().__init__(cs={'left':T1, 'right':T2})
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a) \
                                       and self.comps.right.in_poss(self.poss).query(a)]
    def in_poss(self,poss):
        self.poss = poss
        return self
        
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

class JoinType(JoinTypeStructure, TypeClass):
    def __init__(self,T1,T2): 
        super().__init__(cs={'left':T1, 'right':T2})
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a), \
                                       lambda a: self.comps.right.in_poss(self.poss).query(a)]
    def in_poss(self,poss):
        self.poss = poss
        return self
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

class FunType(FunTypeStructure, TypeClass):
    def __init__(self,T1,T2): 
        super().__init__(cs={'domain':T1, 'range':T2})
        self.witness_conditions = [lambda f: isinstance(f,Fun) \
                                        and f.domain_type == self.comps.domain \
                                        and self.comps.range.query(f.app(self.comps.domain.create_hypobj()))]
    def in_poss(self,poss):
        return self
    

class ListType(ListTypeStructure, TypeClass):
    def __init__(self,T):
        super().__init__(cs={'base_type':T})
        self.witness_conditions = [lambda l: isinstance(l,list) and forall(l, lambda x: T.in_poss(self.poss).query(x))]
    def in_poss(self,poss):
        self.poss = poss
        return self

class SingletonType(SingletonTypeStructure, TypeClass):
    def __init__(self,T,a):
        super().__init__(cs={'base_type':T, 'obj':a})
        self.witness_conditions = [lambda x: show(x) == show(a) and T.query(x),\
                                   lambda x: isinstance(a,LazyObj)\
                                             and show(x) == show(a.eval()) and T.in_poss(self.poss).query(x)]
    def in_poss(self,poss):
        self.poss = poss
        return self
    def create(self):
        self.judge(self.comps.obj)
        return self.comps.obj
    def create_hypobj(self):
        if hasattr(self.comps.obj, 'eval'):
            return self.comps.obj.eval()
        else:
            return self.comps.obj


__all__ = [
    "PTypeClass",
    "PType",
    "MeetType",
    "JoinType",
    "FunType",
    "ListType",
    "SingletonType",
]
