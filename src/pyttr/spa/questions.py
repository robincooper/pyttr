"""Question representations and operations from the SPA-TTR QA proposal."""

from __future__ import annotations

from dataclasses import dataclass

import torchhd

from ..core.compound_types import PTypeClassStructure
from ..core.terms import Fun
from .encoding import Codebook, Encoder


@dataclass(frozen=True)
class EncodedQuestion:
    """An HRR encoding of a one-place TTR question."""

    pointer: object
    body: object
    answer_path: object
    answer_type: object


class QuestionEncoder:
    """Encode and operate on one-place TTR wh-questions using HRR.

    A generic :class:`~pyttr.spa.Encoder` represents a ``Fun`` structurally.
    This encoder instead follows Larsson et al. (2025): the abstracted argument
    is represented by the HRR identity vector and ``lambdapath`` identifies the
    argument role where an answer is inserted or extracted.
    """

    def __init__(self, codebook: Codebook):
        if codebook.vsa != "HRR":
            raise ValueError("QuestionEncoder currently requires vsa='HRR'")
        self.codebook = codebook
        self.encoder = Encoder(codebook)
        self._identity = torchhd.identity(
            1, codebook.dimensions, vsa=codebook.vsa
        )[0]

    def encode(self, question: Fun) -> EncodedQuestion:
        """Encode ``lambda v:T. predicate(..., v, ...)`` as an SPA question."""
        if not isinstance(question, Fun) or not isinstance(question.body, PTypeClassStructure):
            raise TypeError("questions must be Fun objects with a predicate-type body")

        positions = [
            index for index, argument in enumerate(question.body.comps.args)
            if argument == question.var
        ]
        if len(positions) != 1:
            raise ValueError("a one-place question must abstract exactly one body argument")

        answer_path = self._argument_role(positions[0])
        body = self._encode_ptype(question.body, identity_at=positions[0])
        answer_type = self.encoder.encode(question.domain_type)
        pointer = self.encoder.bundle(
            (
                self.encoder.bind(self._role("lambdapath"), answer_path),
                self.encoder.bind(self._role("lambdatype"), answer_type),
                self.encoder.bind(self._role("body"), body),
            )
        )
        return EncodedQuestion(pointer, body, answer_path, answer_type)

    def encode_proposition(self, proposition: PTypeClassStructure):
        """Encode a fully instantiated categorical or probabilistic ptype."""
        if not isinstance(proposition, PTypeClassStructure):
            raise TypeError("propositions must be predicate types")
        return self._encode_ptype(proposition)

    def apply(self, question: EncodedQuestion, answer: str):
        """Apply an answer to a question using the paper's HRR substitution."""
        body = self._unbind(question.pointer, self._role("body"))
        path = self._unbind(question.pointer, self._role("lambdapath"))
        path = self.cleanup(path, (question.answer_path,))[1]
        return body - path + self.encoder.bind(path, self.entity(answer))

    def extract(self, question: EncodedQuestion, proposition):
        """Extract the answer-position pointer from a matching proposition."""
        path = self._unbind(question.pointer, self._role("lambdapath"))
        path = self.cleanup(path, (question.answer_path,))[1]
        return self._unbind(proposition, path)

    def entity(self, name: str):
        """Return the pointer for an individual or other atomic answer."""
        return self.codebook.pointer_for(f"entity:{name}")

    def cleanup(self, pointer, candidates):
        """Return the highest-similarity candidate index and pointer."""
        candidate_list = tuple(candidates)
        if not candidate_list:
            raise ValueError("cleanup requires at least one candidate")
        scores = [self.encoder.similarity(pointer, candidate) for candidate in candidate_list]
        index = max(range(len(candidate_list)), key=scores.__getitem__)
        return index, candidate_list[index]

    def _encode_ptype(self, proposition: PTypeClassStructure, *, identity_at: int | None = None):
        fields = [
            self.encoder.bind(
                self._role("pred"),
                self.codebook.pointer_for(f"predicate:{proposition.comps.pred.name}"),
            )
        ]
        for index, argument in enumerate(proposition.comps.args):
            filler = self._identity if index == identity_at else self._argument(argument)
            fields.append(self.encoder.bind(self._argument_role(index), filler))
        return self.encoder.bundle(fields)

    def _argument(self, argument):
        if isinstance(argument, str):
            return self.entity(argument)
        return self.encoder.encode(argument)

    def _unbind(self, pointer, role):
        return torchhd.bind(pointer, torchhd.inverse(role))

    def _role(self, name: str):
        return self.codebook.pointer_for(f"qa:role:{name}")

    def _argument_role(self, index: int):
        return self._role(f"arg{index + 1}")
