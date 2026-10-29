"""Compatibility wrapper for the legacy top-level ``ttrtypes`` module."""

from importlib import import_module

_module = import_module("pyttr.ttrtypes")
globals().update(
    {name: getattr(_module, name) for name in dir(_module) if not name.startswith("__")}
)
__all__ = [name for name in globals() if not name.startswith("_")]
