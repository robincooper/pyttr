import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr.records import Rec
from pyttr.utils import show, to_latex


class RecTests(unittest.TestCase):
    def test_nested_dicts_become_records(self):
        rec = Rec({"f": {"g": "a"}})

        self.assertIsInstance(rec.f, Rec)
        self.assertEqual(rec.pathvalue("f.g"), "a")

    def test_substitution_recurses_through_nested_records(self):
        rec = Rec({"f": {"g": "a"}, "h": "b"})

        self.assertEqual(show(rec.subst("a", "z")), "{f = {g = z}, h = b}")

    def test_nested_records_can_be_folded_at_a_selected_depth(self):
        rec = Rec({"object": {"id": "a", "data": {"f1": 0.25, "f2": 0.5}}})

        self.assertEqual(
            show(rec, max_record_depth=1),
            "{object = {...}}",
        )
        self.assertEqual(
            show(rec, max_record_depth=2),
            "{object = {id = a, data = {...}}}",
        )
        self.assertIn(
            r"\text{data} &=& \left[\cdots\right]",
            to_latex(rec, max_record_depth=2),
        )

    def test_record_depth_limit_applies_through_collections(self):
        rec = Rec({"evidence": (Rec({"f1": 0.25}),)})

        self.assertEqual(show(rec, max_record_depth=1), "{evidence = ({...})}")

    def test_record_depth_must_be_non_negative(self):
        with self.assertRaisesRegex(ValueError, "max_record_depth"):
            show(Rec(), max_record_depth=-1)

    def test_flatten_and_unflatten_round_trip(self):
        rec = Rec({"f": {"g": "a"}, "h": "b"})

        self.assertEqual(show(rec.flatten()), "{f.g = a, h = b}")
        self.assertEqual(show(rec.flatten().unflatten()), show(rec))

    def test_relabel_returns_new_record(self):
        rec = Rec({"f": "a", "g": "b"})

        relabeled = rec.relabel("f", "z")

        self.assertEqual(show(rec), "{f = a, g = b}")
        self.assertEqual(show(relabeled), "{g = b, z = a}")

    def test_fields_are_not_stored_directly_on_instance_dict(self):
        rec = Rec({"x": "a"})

        self.assertNotIn("x", rec.__dict__)
        self.assertEqual(rec["x"], "a")
        self.assertEqual(rec.x, "a")

    def test_label_can_match_method_name(self):
        rec = Rec({"show": "label-value"})

        self.assertEqual(rec.pathvalue("show"), "label-value")
        self.assertEqual(rec["show"], "label-value")
        self.assertTrue(callable(rec.show))
        self.assertEqual(show(rec), "{show = label-value}")

    def test_mapping_api(self):
        rec = Rec({"x": "a"})

        self.assertIn("x", rec)
        self.assertEqual(rec.get("x"), "a")
        self.assertEqual(rec.get("missing", "fallback"), "fallback")
        self.assertEqual(list(rec.labels()), ["x"])
        self.assertEqual(list(rec.items()), [("x", "a")])

        rec["y"] = "b"
        self.assertEqual(rec["y"], "b")
        self.assertEqual(rec.pop("y"), "b")
        self.assertNotIn("y", rec)

    def test_duplicate_label_warns_and_keeps_existing_value(self):
        rec = Rec({"x": "a"})

        with self.assertWarnsRegex(UserWarning, '"x" is already a label'):
            result = rec.addfield("x", "b")

        self.assertIsNone(result)
        self.assertEqual(rec["x"], "a")


if __name__ == "__main__":
    unittest.main()
