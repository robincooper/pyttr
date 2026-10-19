"""SPA model and witness-cache support for TTR type judgements."""

from __future__ import annotations

import torchhd

from ..core.records import Rec
from ..core.record_types import RecTypeStructure
from ..core.terms import Fun
from ..core.type_core import TypeClass
from .encoding import Codebook, Encoder


class WitnessCache:
    """A type-indexed VSA cache of known witnesses.

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

    def query(self, witness: str | Rec | dict, type_: TypeClass) -> float:
        """Return SPA evidence for ``witness : type_``.

        For a record type, this recursively checks its fields and resolves
        dependent fields. Otherwise, the witness must be a string and this
        returns its similarity to the noisy witness bundle recovered for the
        type.
        """
        if isinstance(type_, RecTypeStructure):
            return _RecordJudger(self).query(witness, type_)
        if not isinstance(witness, str):
            raise TypeError("witness-cache witnesses must be strings")
        key = self._type_key(type_)
        if key not in self._entries:
            return 0.0
        recovered = self._unbind(self._cache_pointer(), self._type_pointers[key])
        return self.encoder.similarity(recovered, self._witness(witness))

    def judges(
        self,
        witness: str | Rec | dict,
        type_: TypeClass,
        *,
        threshold: float,
    ) -> bool:
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
        return self.codebook.pointer_for(f"entity:{witness}")


class _RecordJudger:
    """Resolve and judge concrete records against TTR record types.

    The record's labelled structure remains explicit during judgment.  Basic
    and predicate-type fields are checked through :class:`WitnessCache`; a
    dependent field resolves its stored function against the record values
    named in its dependency list before that SPA lookup.  A record score is
    the minimum field score: every required field must have evidence.
    """

    def __init__(self, witness_cache: WitnessCache):
        self.witness_cache = witness_cache

    def query(self, record: Rec | dict, record_type: RecTypeStructure) -> float:
        """Return the weakest SPA evidence score among required record fields."""
        return self.explain(record, record_type)["score"]

    def explain(self, record: Rec | dict, record_type: RecTypeStructure) -> dict:
        """Return overall and per-field evidence for a record judgment."""
        record = self._as_record(record)
        if not isinstance(record_type, RecTypeStructure):
            raise TypeError("record_type must be a TTR RecType")

        fields = []
        for label, field_type in record_type.comps.items():
            if label not in record:
                fields.append({"label": label, "score": 0.0, "expected": field_type})
                continue
            value = record[label]
            expected, dependency_score = self._resolve_field_type(
                record, field_type
            )
            field_score = min(dependency_score, self._field_score(value, expected))
            fields.append({
                "label": label,
                "score": field_score,
                "expected": expected,
            })

        score = min((field["score"] for field in fields), default=1.0)
        return {"score": score, "fields": tuple(fields)}

    def _field_score(self, value, expected) -> float:
        if isinstance(expected, RecTypeStructure):
            if not isinstance(value, (Rec, dict)):
                return 0.0
            return self.witness_cache.query(value, expected)
        if not isinstance(expected, TypeClass):
            raise TypeError("resolved record fields must be TTR types")
        if not isinstance(value, str):
            raise TypeError("SPA witness-cache field values must be strings")
        return self.witness_cache.query(value, expected)

    def _resolve_field_type(self, record: Rec, field_type):
        if not isinstance(field_type, tuple):
            return field_type, 1.0
        if len(field_type) != 2 or not isinstance(field_type[1], list):
            raise TypeError("dependent fields must be (function, labels) pairs")

        function, dependencies = field_type
        dependency_score = 1.0
        for label in dependencies:
            if not isinstance(label, str):
                raise TypeError("SPA record dependencies must be field labels")
            if label not in record:
                return function, 0.0
            if not isinstance(function, Fun):
                raise TypeError("dependent field has more arguments than its function")
            value = record[label]
            dependency_score = min(
                dependency_score, self._field_score(value, function.domain_type)
            )
            function = function.app(value)
        return function, dependency_score

    @staticmethod
    def _as_record(record: Rec | dict) -> Rec:
        if isinstance(record, Rec):
            return record
        if isinstance(record, dict):
            return Rec(record)
        raise TypeError("record must be a TTR Rec or dictionary")


class SPAModel:
    """An approximate SPA interpretation of TTR judgments.

    ``SPAModel`` owns a codebook, the structural encoder implementing
    :math:`\\sigma`, and a witness cache. A judgment has similarity evidence
    rather than a purely symbolic truth value; ``threshold`` supplies the
    model's default decision boundary.
    """

    def __init__(self, codebook: Codebook, *, threshold: float = 0.1):
        if not isinstance(codebook, Codebook):
            raise TypeError("codebook must be a SPA Codebook")
        self.codebook = codebook
        self.encoder = Encoder(codebook)
        self.witness_cache = WitnessCache(codebook)
        self.threshold = threshold

    def encode(self, value):
        """Return the structural SPA encoding ``sigma(value)``."""
        return self.encoder.encode(value)

    def judge(self, witness: str, type_: TypeClass) -> None:
        """Record an atomic witness judgment in this model."""
        self.witness_cache.judge(witness, type_)

    def query(self, witness: str | Rec | dict, type_: TypeClass) -> float:
        """Return SPA evidence for a TTR judgment."""
        return self.witness_cache.query(witness, type_)

    def explain(self, witness: str | Rec | dict, type_: TypeClass) -> dict:
        """Return field-level evidence for a record judgment.

        Atomic judgments have no internal field structure and are represented
        by a single score.
        """
        if isinstance(type_, RecTypeStructure):
            return _RecordJudger(self.witness_cache).explain(witness, type_)
        return {"score": self.query(witness, type_), "fields": ()}

    def judges(
        self,
        witness: str | Rec | dict,
        type_: TypeClass,
        *,
        threshold: float | None = None,
    ) -> bool:
        """Return whether evidence meets the given or model threshold."""
        return self.query(witness, type_) >= (
            self.threshold if threshold is None else threshold
        )

    def members(self, type_: TypeClass):
        """Return witnesses registered for a non-record type, ranked by evidence."""
        return self.witness_cache.members(type_)
