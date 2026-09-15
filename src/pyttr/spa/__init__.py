"""Semantic Pointer Architecture encodings for TTR objects.

This package represents existing TTR objects as hypervectors.  It does not
define another family of TTR types: construct types through
``pyttr.categorical`` or ``pyttr.probabilistic`` and encode them here.
"""

from .encoding import Codebook, Encoder

__all__ = ["Codebook", "Encoder"]
