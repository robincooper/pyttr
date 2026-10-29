"""Reusable compound type structure, independent of judgment semantics."""
from .type_core import TypeClass, logtype, logtype_t
from .terms import Pred
from .model import add_to_model
from ..utils import show, to_latex, substitute, trace

class PTypeClassStructure:
    def show(self):
        return self.comps.pred.name+'('+', '.join([show(x) for x in self.comps.args])+')'

    def to_latex(self,vars):
        return to_latex(self.comps.pred,vars)+'('+', '.join([to_latex(x,vars) for x in self.comps.args])+')'

    def subst(self,v,a):
        if self == v:
            return a
        else:
            newargs = []
            for arg in self.comps.args:
                if arg == v: newargs.append(a)
                elif isinstance(arg,str): newargs.append(arg)
                else: newargs.append(substitute(arg,v,a))      #arg.subst(v,a))
            return add_to_model(type(self)(self.comps.pred,newargs), self.poss)

    def eval(self):
        newargs = []
        for arg in self.comps.args:
            if hasattr(arg, 'eval'):
                newargs.append(arg.eval())
            else:
                newargs.append(arg)
        self.comps.args = newargs
        return self

class MeetTypeStructure:
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

    def subst(self,v,a):
        if self == v:
            return a
        else:
            return type(self)(self.comps.left.subst(v,a),self.comps.right.subst(v,a)).in_poss(self.poss)

class JoinTypeStructure:
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

    def subst(self,v,a):
        if self == v:
            return a
        else:
            return type(self)(self.comps.left.subst(v,a),self.comps.right.subst(v,a)).in_poss(self.poss)

class FunTypeStructure:
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
        else: return type(self)(self.comps.domain.subst(v,a),self.comps.range.subst(v,a))

class ListTypeStructure:
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
        else: return type(self)(substitute(self.comps.base_type,v,a))

class SingletonTypeStructure:
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

    def subst(self,v,a):
        if self == v:
            return a
        else: return type(self)(substitute(self.comps.base_type,v,a),substitute(self.comps.obj,v,a))

__all__ = ['PTypeClassStructure', 'MeetTypeStructure', 'JoinTypeStructure', 'FunTypeStructure', 'ListTypeStructure', 'SingletonTypeStructure']
