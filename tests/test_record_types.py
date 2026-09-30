import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr import ttrtypes as ttr
from pyttr.records import Rec


class RecordTypeBehaviorTests(unittest.TestCase):
    def test_nested_record_types_can_be_folded(self):
        nested = ttr.RecType({"object": ttr.RecType({"id": ttr.BType("Ind")})})

        self.assertEqual(nested.show(max_record_depth=1), "{object : {...}}")
        self.assertIn(
            r"\text{object} &:& \left[\cdots\right]",
            nested.to_latex(vars=[], max_record_depth=1),
        )

    def setUp(self):
        ttr.initmodel()

    def test_nested_record_type_paths_resolve_to_nested_fields(self):
        ind = ttr.BType("Ind")
        record_type = ttr.RecType({"person": {"name": ind}})

        self.assertIsInstance(record_type.pathvalue("person"), ttr.RecType)
        self.assertIs(record_type.pathvalue("person.name"), ind)
        self.assertIsNone(record_type.pathvalue("person.missing"))

    def test_dependent_record_type_validation_checks_paths(self):
        ind = ttr.BType("Ind")
        man = ttr.Pred("man", [ind])
        dependency = ttr.Fun("v", ind, ttr.PType(man, ["v"]))

        valid = ttr.RecType({"x": ind, "event": (dependency, ["x"])})
        invalid = ttr.RecType({"x": ind, "event": (dependency, ["missing"])})

        self.assertTrue(valid.validate())
        self.assertFalse(invalid.validate())

    def test_dependent_record_field_query_uses_prior_field_value(self):
        ind = ttr.BType("Ind")
        ind.judge("j")
        ind.judge("k")
        man = ttr.Pred("man", [ind])
        ttr.PType(man, ["j"]).judge("e_j")

        record_type = ttr.RecType(
            {
                "x": ind,
                "event": (ttr.Fun("v", ind, ttr.PType(man, ["v"])), ["x"]),
            }
        )

        self.assertTrue(record_type.query(Rec({"x": "j", "event": "e_j"})))
        self.assertFalse(record_type.query(Rec({"x": "k", "event": "e_j"})))
        self.assertFalse(record_type.query(Rec({"x": "j"})))

    def test_duplicate_record_type_label_warns_and_keeps_existing_value(self):
        ind = ttr.BType("Ind")
        other = ttr.BType("Other")
        record_type = ttr.RecType({"x": ind})

        with self.assertWarnsRegex(UserWarning, '"x" is already a label'):
            record_type.addfield("x", other)

        self.assertIs(record_type.pathvalue("x"), ind)

    def test_record_type_helpers_raise_on_non_record_type_inputs(self):
        ind = ttr.BType("Ind")

        with self.assertRaisesRegex(TypeError, "LabelsRecType is not defined"):
            ttr.LabelsRecType(ind)

        with self.assertRaisesRegex(TypeError, "AttValRecType is not defined"):
            ttr.AttValRecType(ind, "x")

    def test_process_dependent_fields_rejects_unknown_mode(self):
        with self.assertRaisesRegex(ValueError, "not recognized as option"):
            ttr.ProcessDepFields(ttr.RecType(), Rec(), ttr.RecType(), "other")


if __name__ == "__main__":
    unittest.main()
