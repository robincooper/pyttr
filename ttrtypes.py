"""Compatibility wrapper for the legacy top-level ``ttrtypes`` module."""

from importlib import import_module
from pathlib import Path
import sys

_SRC = Path(__file__).resolve().parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

_module = import_module("pyttr.ttrtypes")
globals().update(
    {name: getattr(_module, name) for name in dir(_module) if not name.startswith("__")}
)
__all__ = [name for name in globals() if not name.startswith("_")]
