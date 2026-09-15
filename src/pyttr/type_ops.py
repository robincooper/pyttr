"""Compatibility exports; implementation lives in :mod:`pyttr.core.type_ops`."""

from .core.type_ops import (
    equal,
    ti_apply,
    merge_dep_types,
    combine_dep_types,
    subtype_of_dep_types,
)

__all__ = ['equal', 'ti_apply', 'merge_dep_types', 'combine_dep_types', 'subtype_of_dep_types']
