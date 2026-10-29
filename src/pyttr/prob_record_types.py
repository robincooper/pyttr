"""Compatibility exports; implementation lives in :mod:`pyttr.probabilistic.record_types`."""

from .probabilistic.record_types import (
    RecType,
    RecOfRecType,
    QueryField,
)

__all__ = ['RecType', 'RecOfRecType', 'QueryField']
