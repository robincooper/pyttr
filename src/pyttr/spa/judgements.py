"""SPA witness-cache support for basic TTR type judgements."""

from __future__ import annotations

import torchhd

from ..core.type_core import TypeClass
from .encoding import Codebook, Encoder


class WitnessCache:
    """A type-indexed VSA cache of known atomic witnesses.

    The cache implements the witness-memory pattern from Larsson et al.
    (2023): each type pointer is bound to a superposition of its witness
    pointers. Unbinding a type recovers a noisy witness bundle, which can be
    compared to a candidate or cleaned up against the recorded witnesses.
    """

    def __init__(self, codebook: Codebook):
        self.codebook = codebook
        self.encoder = Encoder(codebook)
        self._entries: dict[str, dict[str, object]] = {}
        self._type_pointers: dict[str, object] = {}

    def judge(self, witness: str, type_: TypeClass) -> None:
        """Record the SPA-TTR judgement ``witness : type_``."""
        key = self._type_key(type_)
        self._entries.setdefault(key, {})[witness] = self._witness(witness)
        self._type_pointers.setdefault(key, self.encoder.encode(type_))

    def query(self, witness: str, type_: TypeClass) -> float:
        """Return similarity evidence for ``witness : type_``.

        A score near zero indicates no support from this cache. Scores for
        stored witnesses are lower than one because unbinding recovers a
        superposition rather than an individual pointer.
        """
        key = self._type_key(type_)
        if key not in self._entries:
            return 0.0
        recovered = self._unbind(self._cache_pointer(), self._type_pointers[key])
        return self.encoder.similarity(recovered, self._witness(witness))

    def judges(self, witness: str, type_: TypeClass, *, threshold: float) -> bool:
        """Return whether the cache evidence for a judgement meets ``threshold``."""
        return self.query(witness, type_) >= threshold

    def members(self, type_: TypeClass):
        """Return stored witnesses ranked by their recovered-cache similarity."""
        key = self._type_key(type_)
        if key not in self._entries:
            return ()
        recovered = self._unbind(self._cache_pointer(), self._type_pointers[key])
        return tuple(sorted(
            (
                (witness, self.encoder.similarity(recovered, pointer))
                for witness, pointer in self._entries[key].items()
            ),
            key=lambda item: item[1],
            reverse=True,
        ))

    def _cache_pointer(self):
        return self.encoder.bundle(
            self.encoder.bind(
                self._type_pointers[key],
                self.encoder.bundle(witnesses.values()),
            )
            for key, witnesses in self._entries.items()
        )

    def _unbind(self, pointer, role):
        return torchhd.bind(pointer, torchhd.inverse(role))

    def _type_key(self, type_: TypeClass) -> str:
        if not isinstance(type_, TypeClass):
            raise TypeError("witness-cache types must be TTR TypeClass instances")
        family = getattr(type_, "_semantic_family", type(type_).__module__)
        return f"{family}:{type_.show()}"

    def _witness(self, witness: str):
        if not isinstance(witness, str):
            raise TypeError("witness-cache witnesses must be strings")
        return self.codebook.pointer_for(f"witness:{witness}")
