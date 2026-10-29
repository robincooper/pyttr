"""Compatibility exports; implementation lives in :mod:`pyttr.probabilistic.type_core`."""

from .probabilistic.type_core import (
    TypeClass,
    Type,
    BTypeClass,
    BType,
)

__all__ = ['TypeClass', 'Type', 'BTypeClass', 'BType']

from .probabilistic.type_core import QUERY_METHODS
