"""Compatibility exports; implementation lives in :mod:`pyttr.core.terms`."""

from .core.terms import (
    Pred,
    Fun,
    HypObj,
    LazyObj,
    AbsPath,
    FunctionApplicationError,
)

__all__ = ['Pred', 'Fun', 'HypObj', 'LazyObj', 'AbsPath', 'FunctionApplicationError']
