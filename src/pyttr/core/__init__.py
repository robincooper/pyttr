"""Shared TTR structures; concrete judgment semantics live in sibling packages."""
from .records import Rec
from .type_core import TypeClass
from .terms import AbsPath, Fun, HypObj, LazyObj, Pred

__all__ = ["Rec", "TypeClass", "AbsPath", "Fun", "HypObj", "LazyObj", "Pred"]
