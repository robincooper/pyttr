"""Indexed associative memory for SPA-TTR propositions."""

from __future__ import annotations

from dataclasses import dataclass

from .questions import EncodedQuestion, QuestionEncoder


@dataclass(frozen=True)
class MemoryMatch:
    """A proposition retrieved from associative memory."""

    label: str
    pointer: object
    index_similarity: float
    proposition_similarity: float


class AssociativeMemory:
    """Store proposition pointers as indexed HRR bindings and retrieve by cue."""

    def __init__(self, question_encoder: QuestionEncoder):
        self.question_encoder = question_encoder
        self.encoder = question_encoder.encoder
        self.codebook = question_encoder.codebook
        self._entries: dict[str, object] = {}

    def add(self, label: str, proposition) -> None:
        """Store a ptype under a stable memory index."""
        if label in self._entries:
            raise ValueError(f"memory already contains {label!r}")
        self._entries[label] = self.question_encoder.encode_proposition(proposition)

    def ranked_propositions(self, question: EncodedQuestion):
        """Rank stored propositions against a question body cue."""
        return tuple(sorted(
            (
                (label, self.encoder.similarity(question.body, pointer))
                for label, pointer in self._entries.items()
            ),
            key=lambda item: item[1],
            reverse=True,
        ))

    def search(self, question: EncodedQuestion) -> MemoryMatch:
        """Retrieve the best matching proposition via indexed HRR memory."""
        if not self._entries:
            raise ValueError("cannot search an empty memory")
        memory = self._memory_pointer()
        index_estimate = self.question_encoder._unbind(memory, question.body)
        labels = tuple(self._entries)
        indices = tuple(self._index(label) for label in labels)
        index_position, cleaned_index = self.question_encoder.cleanup(index_estimate, indices)
        label = labels[index_position]
        recovered = self.question_encoder._unbind(memory, cleaned_index)
        proposition_position, cleaned_proposition = self.question_encoder.cleanup(
            recovered, tuple(self._entries.values())
        )
        proposition_label = labels[proposition_position]
        return MemoryMatch(
            proposition_label,
            cleaned_proposition,
            self.encoder.similarity(index_estimate, cleaned_index),
            self.encoder.similarity(recovered, cleaned_proposition),
        )

    def answer(self, question: EncodedQuestion, candidates: tuple[str, ...]):
        """Retrieve a proposition, extract its answer, and clean it up."""
        match = self.search(question)
        raw_answer = self.question_encoder.extract(question, match.pointer)
        candidate_pointers = tuple(self.question_encoder.entity(name) for name in candidates)
        position, _ = self.question_encoder.cleanup(raw_answer, candidate_pointers)
        scores = tuple(
            (name, self.encoder.similarity(raw_answer, pointer))
            for name, pointer in zip(candidates, candidate_pointers)
        )
        return match, candidates[position], tuple(sorted(scores, key=lambda item: item[1], reverse=True))

    def _memory_pointer(self):
        return self.encoder.bundle(
            self.encoder.bind(self._index(label), pointer)
            for label, pointer in self._entries.items()
        )

    def _index(self, label: str):
        return self.codebook.pointer_for(f"memory:index:{label}")
