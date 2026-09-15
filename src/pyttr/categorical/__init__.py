"""Public API for categorical Type Theory with Records."""
from ..core.records import Rec
from ..core.type_ops import equal
from ..utils import show, to_latex, ttracing
from .model import Possibility, initmodel, showmodel
from .type_core import Type, TypeClass, BType, BTypeClass
from .terms import Pred, Fun, HypObj, LazyObj, AbsPath, FunctionApplicationError
from .compound_types import PType, PTypeClass, MeetType, JoinType, FunType, ListType, SingletonType
from .record_types import RecType
from .string_types import TTRString, TTRStringType, KPlusStringType
from .prelude import Ty, Re, RecTy

__all__ = ['Rec', 'Type', 'TypeClass', 'BType', 'BTypeClass', 'Pred', 'PType',
    'PTypeClass', 'RecType', 'MeetType', 'JoinType', 'FunType', 'ListType',
    'SingletonType', 'Fun', 'HypObj', 'LazyObj', 'AbsPath', 'FunctionApplicationError',
    'Possibility', 'initmodel', 'showmodel', 'equal', 'show', 'to_latex', 'ttracing',
    'TTRString', 'TTRStringType', 'KPlusStringType', 'Ty', 'Re', 'RecTy']
