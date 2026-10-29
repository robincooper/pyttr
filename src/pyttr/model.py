"""Compatibility exports; implementation lives in :mod:`pyttr.core.model`."""

from .core.model import (
    Possibility,
    _M,
    showmodel,
    initmodel,
    add_to_model,
)

__all__ = ['Possibility', '_M', 'showmodel', 'initmodel', 'add_to_model']
