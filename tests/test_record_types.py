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


if __name__ == "__main__":
    unittest.main()
