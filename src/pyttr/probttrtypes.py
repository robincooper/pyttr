"""Compatibility exports for the classic :mod:`pyttr.probttrtypes` module."""

from copy import copy, deepcopy

import inspect
import numpy as np

from . import config, ttrtypes
from .records import Rec
from .ttrtypes import (
    ComputeDepType,
    HypObj,
    LazyObj,
    Pred,
    equal,
    logtype,
    logtype_t,
)
from .utils import apply123, check_stack, forsome, gensym, show, showall, substitute, ttracing
from .probabilistic.model import _M, add_to_model
from .prob_constraints import (
    ConjProb,
    DisjProb,
    PConstraint,
    PDiv,
    PExtreme,
    PMax,
    PMinus,
    PNeg,
    PPlus,
    PRound,
    PSum,
    PTimes,
)
from .prob_type_core import BType, BTypeClass, Type, TypeClass
from .prob_predicates import PType, PTypeClass, matchlist
from .prob_compound_types import JoinType, MeetType, NegType, VarType
from .prob_record_types import QueryField, RecOfRecType, RecType
from .prob_terms import Fun, Possibility


__all__ = [
    "np",
    "inspect",
    "config",
    "ttrtypes",
    "deepcopy",
    "copy",
    "HypObj",
    "LazyObj",
    "equal",
    "Pred",
    "add_to_model",
    "_M",
    "ComputeDepType",
    "Fun",
    "logtype",
    "logtype_t",
    "show",
    "showall",
    "forsome",
    "gensym",
    "check_stack",
    "apply123",
    "ttracing",
    "substitute",
    "Rec",
    "TypeClass",
    "Type",
    "BTypeClass",
    "BType",
    "PTypeClass",
    "PType",
    "matchlist",
    "MeetType",
    "JoinType",
    "RecType",
    "RecOfRecType",
    "QueryField",
    "NegType",
    "VarType",
    "PConstraint",
    "PMax",
    "PExtreme",
    "PSum",
    "PNeg",
    "PRound",
    "PTimes",
    "PDiv",
    "PMinus",
    "PPlus",
    "ConjProb",
    "DisjProb",
    "Possibility",
]
