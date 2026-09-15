"""SPA encodings for TTR structures."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr import categorical as cat
from pyttr.spa import Codebook, Encoder


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


if __name__ == "__main__":
    unittest.main()
