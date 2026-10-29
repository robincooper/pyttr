"""SPA encodings for TTR structures."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr import categorical as cat
from pyttr.spa import (
    AssociativeMemory,
    Codebook,
    Encoder,
    QuestionEncoder,
    SPAModel,
    WitnessCache,
)
from pyttr.records import Rec


class SPAEncodingTests(unittest.TestCase):
    def setUp(self):
        cat.initmodel()
        self.encoder = Encoder(Codebook(dimensions=10_000, seed=7))

    def record_type_parts(self):
        ind = cat.BType("Ind")
        man = cat.Pred("man", [ind])
        run = cat.Pred("run", [ind])
        man_at_x = (cat.Fun("v", ind, cat.PType(man, ["v"])), ["x"])
        run_at_x = (cat.Fun("v", ind, cat.PType(run, ["v"])), ["x"])
        man_type = cat.RecType({"x": ind, "c_man": man_at_x})
        run_type = cat.RecType({"x": ind, "c_run": run_at_x})
        return ind, man_type, run_type

    def test_codebook_is_stable_within_an_encoder(self):
        pointer = self.encoder.codebook.pointer_for("label:x")
        self.assertIs(pointer, self.encoder.codebook.pointer_for("label:x"))

    def test_entity_encoding_is_shared_by_witnesses_and_predicate_arguments(self):
        ind = cat.BType("Ind")
        man = cat.Pred("man", [ind])
        model = SPAModel(self.encoder.codebook)
        model.judge("alice", ind)

        self.assertIs(
            self.encoder.encode("alice"),
            self.encoder.codebook.pointer_for("entity:alice"),
        )
        self.assertIn("entity:alice", self.encoder.codebook._pointers)
        self.encoder.encode(cat.PType(man, ["alice"]))
        self.assertNotIn("variable:alice", self.encoder.codebook._pointers)
        self.encoder.encode(cat.Fun("v", ind, cat.PType(man, ["v"])))
        self.assertIn("variable:v", self.encoder.codebook._pointers)
        self.assertNotIn("entity:v", self.encoder.codebook._pointers)

    def test_merge_encoding_works_across_vsa_models(self):
        ind, man_type, run_type = self.record_type_parts()
        merged = man_type.merge(run_type)
        unrelated = cat.RecType({"y": ind})
        for vsa in ("BSC", "MAP", "HRR"):
            for dimensions in (512, 4_096):
                with self.subTest(vsa=vsa, dimensions=dimensions):
                    encoder = Encoder(
                        Codebook(dimensions=dimensions, vsa=vsa, seed=7)
                    )
                    merged_pointer = encoder.encode(merged)
                    unrelated_similarity = encoder.similarity(
                        merged_pointer, encoder.encode(unrelated)
                    )
                    self.assertGreater(
                        encoder.similarity(merged_pointer, encoder.encode(man_type)),
                        unrelated_similarity,
                    )
                    self.assertGreater(
                        encoder.similarity(merged_pointer, encoder.encode(run_type)),
                        unrelated_similarity,
                    )

    def test_merge_encoding_retains_both_component_types(self):
        ind, man_type, run_type = self.record_type_parts()
        merged = man_type.merge(run_type)
        unrelated = cat.RecType({"y": ind})

        merged_pointer = self.encoder.encode(merged)
        self.assertEqual(set(merged.comps.labels()), {"x", "c_man", "c_run"})
        self.assertGreater(
            self.encoder.similarity(merged_pointer, self.encoder.encode(man_type)),
            self.encoder.similarity(merged_pointer, self.encoder.encode(unrelated)),
        )
        self.assertGreater(
            self.encoder.similarity(merged_pointer, self.encoder.encode(run_type)),
            self.encoder.similarity(merged_pointer, self.encoder.encode(unrelated)),
        )

    def qa_model(self):
        ind = cat.BType("Ind")
        chase = cat.Pred("chase", [ind, ind])
        see = cat.Pred("see", [ind, ind])
        like = cat.Pred("like", [ind, ind])
        question_encoder = QuestionEncoder(
            Codebook(dimensions=10_000, vsa="HRR", seed=7)
        )
        memory = AssociativeMemory(question_encoder)
        propositions = {
            "p1": cat.PType(chase, ["dog", "cat"]),
            "p2": cat.PType(chase, ["dog", "cow"]),
            "p3": cat.PType(see, ["dog", "mouse"]),
            "p4": cat.PType(see, ["mouse", "cow"]),
            "p5": cat.PType(like, ["cat", "mouse"]),
            "p6": cat.PType(like, ["dog", "cow"]),
        }
        for label, proposition in propositions.items():
            memory.add(label, proposition)
        return ind, chase, like, question_encoder, memory

    def test_question_application_matches_categorical_ttr(self):
        ind, chase, _, question_encoder, _ = self.qa_model()
        question = cat.Fun("v", ind, cat.PType(chase, ["dog", "v"]))
        categorical_result = question.app("cat")
        encoded_question = question_encoder.encode(question)
        spa_result = question_encoder.apply(encoded_question, "cat")
        expected = question_encoder.encode_proposition(categorical_result)
        unrelated = question_encoder.encode_proposition(cat.PType(chase, ["cat", "dog"]))

        self.assertEqual(categorical_result.show(), "chase(dog, cat)")
        self.assertGreater(
            question_encoder.encoder.similarity(spa_result, expected),
            question_encoder.encoder.similarity(spa_result, unrelated),
        )

    def test_question_extraction_and_associative_memory(self):
        ind, chase, like, question_encoder, memory = self.qa_model()
        candidates = ("dog", "cat", "cow", "mouse")

        cat_likes = question_encoder.encode(
            cat.Fun("v", ind, cat.PType(like, ["cat", "v"]))
        )
        match, answer, scores = memory.answer(cat_likes, candidates)
        self.assertEqual(match.label, "p5")
        self.assertEqual(answer, "mouse")
        self.assertEqual(scores[0][0], "mouse")

        dog_chases = question_encoder.encode(
            cat.Fun("v", ind, cat.PType(chase, ["dog", "v"]))
        )
        ranked = memory.ranked_propositions(dog_chases)
        self.assertEqual({label for label, _ in ranked[:2]}, {"p1", "p2"})
        match, answer, _ = memory.answer(dog_chases, candidates)
        self.assertIn(match.label, {"p1", "p2"})
        self.assertIn(answer, {"cat", "cow"})

        likes_cow = question_encoder.encode(
            cat.Fun("v", ind, cat.PType(like, ["v", "cow"]))
        )
        match, answer, scores = memory.answer(likes_cow, candidates)
        self.assertEqual(match.label, "p6")
        self.assertEqual(answer, "dog")
        self.assertEqual(scores[0][0], "dog")

    def test_witness_cache_supports_basic_type_judgements(self):
        ind = cat.BType("Ind")
        color = cat.BType("Color")
        for vsa in ("BSC", "MAP", "HRR", "FHRR"):
            with self.subTest(vsa=vsa):
                cache = WitnessCache(Codebook(dimensions=10_000, vsa=vsa, seed=7))
                cache.judge("alice", ind)
                cache.judge("bob", ind)
                cache.judge("red", color)

                alice_score = cache.query("alice", ind)
                self.assertGreater(alice_score, cache.query("carol", ind))
                self.assertGreater(alice_score, cache.query("red", ind))
                self.assertTrue(cache.judges("alice", ind, threshold=0.1))
                self.assertFalse(cache.judges("carol", ind, threshold=0.1))
                self.assertEqual(
                    {witness for witness, _ in cache.members(ind)}, {"alice", "bob"}
                )
                self.assertEqual(cache.members(color)[0][0], "red")

    def test_spa_model_resolves_dependent_predicate_fields(self):
        ind = cat.BType("Ind")
        man = cat.Pred("man", [ind])
        record_type = cat.RecType({
            "x": ind,
            "c_man": (cat.Fun("v", ind, cat.PType(man, ["v"])), ["x"]),
        })
        model = SPAModel(Codebook(dimensions=10_000, vsa="HRR", seed=7))
        model.judge("alice", ind)
        model.judge("e_alice_man", cat.PType(man, ["alice"]))

        valid = Rec({"x": "alice", "c_man": "e_alice_man"})
        wrong_dependency = Rec({"x": "bob", "c_man": "e_alice_man"})
        missing_field = Rec({"x": "alice"})

        self.assertGreater(model.query(valid, record_type), 0.1)
        self.assertTrue(model.judges(valid, record_type))
        self.assertFalse(model.judges(wrong_dependency, record_type))
        self.assertFalse(model.judges(missing_field, record_type))
        self.assertEqual(
            model.witness_cache.query(valid, record_type), model.query(valid, record_type)
        )


if __name__ == "__main__":
    unittest.main()
