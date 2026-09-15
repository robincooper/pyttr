"""Compatibility exports; implementation lives in :mod:`pyttr.categorical.record_types`."""

from .categorical.record_types import (
    RecType,
    LabelsRecType,
    AttValRecType,
    RecOfRecType,
    QueryField,
    ComputeDepType,
    CheckField,
    CheckPathList,
    CheckPath,
    ProcessDepFields,
)

__all__ = ['RecType', 'LabelsRecType', 'AttValRecType', 'RecOfRecType', 'QueryField', 'ComputeDepType', 'CheckField', 'CheckPathList', 'CheckPath', 'ProcessDepFields']
