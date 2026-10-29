"""Categorical model API."""
from ..core.model import Possibility, _M, add_to_model, showmodel


def initmodel():
    """Clear only the categorical default model."""
    _M.model.clear()

__all__ = ["Possibility", "_M", "add_to_model", "initmodel", "showmodel"]
