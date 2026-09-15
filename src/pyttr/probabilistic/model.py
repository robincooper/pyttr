"""Probabilistic models have their own default type registry."""
from ..core.model import add_to_model as _add_to_model, register_default_model
from ..utils import show
from .terms import Possibility

_M = register_default_model(Possibility('_ProbModel_'))

def add_to_model(T, m=_M):
    return _add_to_model(T, m)

def initmodel():
    _M.model.clear()

def showmodel(m=_M):
    return show(m)

__all__ = ['Possibility', '_M', 'add_to_model', 'initmodel', 'showmodel']
