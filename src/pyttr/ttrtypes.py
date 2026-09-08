"""Compatibility exports for the classic :mod:`pyttr.ttrtypes` module."""

from collections import deque
from copy import copy

from .model import Possibility, _M, add_to_model, initmodel, showmodel
from .records import Rec
from .utils import check_stack, forall, forsome, gensym, show, showall, some_condition, substitute, to_latex, ttracing
from .type_core import BType, BTypeClass, Type, TypeClass, logtype, logtype_t
from .terms import AbsPath, Fun, FunctionApplicationError, HypObj, LazyObj, Pred
from .type_ops import combine_dep_types, equal, merge_dep_types, subtype_of_dep_types, ti_apply
from .compound_types import FunType, JoinType, ListType, MeetType, PType, PTypeClass, SingletonType
from .record_types import (
    AttValRecType,
    CheckField,
    CheckPath,
    CheckPathList,
    ComputeDepType,
    LabelsRecType,
    ProcessDepFields,
    QueryField,
    RecOfRecType,
    RecType,
)
from .string_types import KPlusStringType, TTRString, TTRStringType
from .prelude import Re, RecTy, Ty, create_method_rec, create_method_type


__all__ = [
    "Possibility",
    "_M",
    "copy",
    "deque",
    "Rec",
    "gensym",
    "some_condition",
    "forall",
    "forsome",
    "substitute",
    "show",
    "to_latex",
    "showall",
    "ttracing",
    "check_stack",
    "showmodel",
    "initmodel",
    "add_to_model",
    "TypeClass",
    "Type",
    "BTypeClass",
    "BType",
    "logtype",
    "logtype_t",
    "Pred",
    "Fun",
    "HypObj",
    "LazyObj",
    "AbsPath",
    "FunctionApplicationError",
    "equal",
    "ti_apply",
    "merge_dep_types",
    "combine_dep_types",
    "subtype_of_dep_types",
    "PTypeClass",
    "PType",
    "MeetType",
    "JoinType",
    "FunType",
    "ListType",
    "SingletonType",
    "RecType",
    "LabelsRecType",
    "AttValRecType",
    "RecOfRecType",
    "QueryField",
    "ComputeDepType",
    "CheckField",
    "CheckPathList",
    "CheckPath",
    "ProcessDepFields",
    "TTRString",
    "TTRStringType",
    "KPlusStringType",
    "Ty",
    "Re",
    "RecTy",
    "create_method_type",
    "create_method_rec",
]
