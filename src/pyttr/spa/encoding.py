"""TorchHD encodings for the structured part of TTR.

The initial encoding follows the role--filler scheme used in SPA: a record
type is a superposition of bindings from its field labels to the encodings of
their types.  ``Codebook`` owns the stable random pointers used for labels,
types, predicates, and variables.
"""

from __future__ import annotations

from collections.abc import Iterable

import torch
import torchhd

from ..core.compound_types import PTypeClassStructure
from ..core.record_types import RecTypeStructure
from ..core.terms import Fun, Pred
from ..core.type_core import TypeClass


class Codebook:
    """A seeded mapping from symbolic names to TorchHD hypervectors.

    ``vsa`` is forwarded to TorchHD, for example ``"MAP"``, ``"BSC"``, or
    ``"HRR"``.
    """

    def __init__(
        self,
        dimensions: int = 10_000,
        *,
        vsa: str = "MAP",
        seed: int | None = None,
    ):
        if dimensions < 1:
            raise ValueError("dimensions must be positive")
        self.dimensions = dimensions
        self.vsa = vsa
        self._pointers = {}
        self._generator = torch.Generator(device="cpu")
        if seed is not None:
            self._generator.manual_seed(seed)

    def pointer_for(self, name: str):
        """Return the stable pointer assigned to ``name`` in this codebook."""
        if not isinstance(name, str):
            raise TypeError("codebook names must be strings")
        if name not in self._pointers:
            self._pointers[name] = torchhd.random(
                1, self.dimensions, vsa=self.vsa, generator=self._generator
            )[0]
        return self._pointers[name]


class Encoder:
    """Encode categorical or probabilistic TTR structures as MAP hypervectors."""

    def __init__(self, codebook: Codebook):
        self.codebook = codebook

    def encode(self, value):
        """Encode a supported TTR structure or a symbolic term.

        Record types, predicate types, dependent fields, and functions retain
        their internal structure. Basic types and otherwise atomic TTR types
        receive a stable codebook pointer.
        """
        if isinstance(value, RecTypeStructure):
            return self.encode_record_type(value)
        if isinstance(value, PTypeClassStructure):
            return self._encode_predicate_type(value)
        if isinstance(value, Fun):
            return self._encode_function(value)
        if isinstance(value, Pred):
            return self.codebook.pointer_for(f"predicate:{value.name}")
        if isinstance(value, tuple):
            return self._encode_dependent_field(value)
        if isinstance(value, str):
            return self.codebook.pointer_for(f"variable:{value}")
        if isinstance(value, TypeClass):
            return self.codebook.pointer_for(f"type:{value.show()}")
        raise TypeError(f"cannot encode {type(value).__name__}")

    def encode_record_type(self, record_type: RecTypeStructure):
        """Encode a record type as label--type bindings in superposition."""
        fields = [
            self.bind(self.codebook.pointer_for(f"label:{label}"), self.encode(field))
            for label, field in record_type.comps.items()
        ]
        return self.bundle(fields)

    def bind(self, role, filler):
        """Bind a role and filler pointer."""
        return torchhd.bind(role, filler)

    def bundle(self, pointers: Iterable):
        """Superpose pointers, preserving the MAP tensor representation."""
        iterator = iter(pointers)
        try:
            result = next(iterator)
        except StopIteration:
            return torchhd.empty(
                1, self.codebook.dimensions, vsa=self.codebook.vsa
            )[0]
        for pointer in iterator:
            result = torchhd.bundle(result, pointer)
        return result

    @staticmethod
    def similarity(left, right) -> float:
        """Return cosine similarity between two semantic pointers."""
        return float(torchhd.cosine_similarity(left, right).item())

    def _encode_predicate_type(self, predicate_type: PTypeClassStructure):
        predicate = predicate_type.comps.pred
        fields = [
            self.bind(
                self.codebook.pointer_for("role:predicate"),
                self.encode(predicate),
            )
        ]
        for index, argument in enumerate(predicate_type.comps.args):
            fields.append(
                self.bind(
                    self.codebook.pointer_for(f"role:argument:{index}"),
                    self.encode(argument),
                )
            )
        return self.bundle(fields)

    def _encode_function(self, function: Fun):
        return self.bundle(
            (
                self.bind(
                    self.codebook.pointer_for("role:bound-variable"),
                    self.codebook.pointer_for(f"variable:{function.var}"),
                ),
                self.bind(
                    self.codebook.pointer_for("role:domain"),
                    self.encode(function.domain_type),
                ),
                self.bind(
                    self.codebook.pointer_for("role:body"),
                    self.encode(function.body),
                ),
            )
        )

    def _encode_dependent_field(self, field: tuple):
        if len(field) != 2 or not isinstance(field[1], list):
            raise TypeError("dependent fields must be (function, labels) pairs")
        function, labels = field
        dependencies = self.bundle(
            self.codebook.pointer_for(f"dependency:{label}") for label in labels
        )
        return self.bundle(
            (
                self.bind(
                    self.codebook.pointer_for("role:dependent-function"),
                    self.encode(function),
                ),
                self.bind(
                    self.codebook.pointer_for("role:dependencies"), dependencies
                ),
            )
        )
