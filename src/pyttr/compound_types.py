"""Compatibility exports; implementation lives in :mod:`pyttr.categorical.compound_types`."""

from .categorical.compound_types import (
    PTypeClass,
    PType,
    MeetType,
    JoinType,
    FunType,
    ListType,
    SingletonType,
)

__all__ = ['PTypeClass', 'PType', 'MeetType', 'JoinType', 'FunType', 'ListType', 'SingletonType']
