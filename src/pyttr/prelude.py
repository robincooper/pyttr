"""Compatibility exports; implementation lives in :mod:`pyttr.categorical.prelude`."""

from .categorical.prelude import (
    Ty,
    Re,
    RecTy,
    create_method_type,
    create_method_rec,
)

__all__ = ['Ty', 'Re', 'RecTy', 'create_method_type', 'create_method_rec']
