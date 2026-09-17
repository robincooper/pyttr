"""Semantic Pointer Architecture encodings for TTR objects.

This package represents existing TTR objects as hypervectors.  It does not
define another family of TTR types: construct types through
``pyttr.categorical`` or ``pyttr.probabilistic`` and encode them here.
"""

from .encoding import Codebook, Encoder
from .judgements import SPAModel, WitnessCache
from .memory import AssociativeMemory, MemoryMatch
from .questions import EncodedQuestion, QuestionEncoder

__all__ = [
    "AssociativeMemory",
    "Codebook",
    "EncodedQuestion",
    "Encoder",
    "MemoryMatch",
    "QuestionEncoder",
    "SPAModel",
    "WitnessCache",
]
