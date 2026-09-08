from .records import Rec
from .record_types import RecType
from .type_core import Type, TypeClass, logtype, logtype_t
from .utils import gensym

Ty = Type('Ty') 
Ty.witness_conditions = [lambda T : isinstance(T,TypeClass)]
Ty.learn_witness_condition = logtype.__get__(Ty,Ty.__class__)
Ty.learn_witness_type = logtype_t.__get__(Ty,Ty.__class__)


def create_method_type(self):
    a = gensym('_T')
    self.judge(a)
    return a


Ty.create = create_method_type.__get__(Ty, Ty.__class__)#MethodType(create_method_type,Ty,Type)

Re = Type('Re')
Re.witness_conditions = [lambda r: isinstance(r,Rec)]
Re.learn_witness_condition = logtype.__get__(Re,Re.__class__)
Re.learn_witness_type = logtype_t.__get__(Re,Re.__class__)


def create_method_rec(self):
    a = gensym('_r')
    self.judge(a)
    return a


Re.create = create_method_rec.__get__(Re, Re.__class__)#MethodType(create_method_rec,Re,Type)

RecTy = Type('RecTy')
RecTy.witness_conditions = [lambda T: isinstance(T,RecType)]
RecTy.supertype_cache = [Ty]
RecTy.learn_witness_condition = logtype.__get__(RecTy,RecTy.__class__)
RecTy.learn_witness_type = logtype_t.__get__(RecTy,RecTy.__class__)
RecTy.create = create_method_type.__get__(RecTy, RecTy.__class__)#MethodType(create_method_type,RecTy,Type)


__all__ = [
    "Ty",
    "Re",
    "RecTy",
    "create_method_type",
    "create_method_rec",
]
