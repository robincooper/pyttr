import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))


class PackageImportTests(unittest.TestCase):
    def test_package_modules_import(self):
        from pyttr.records import Rec
        from pyttr import probttrtypes, ttrtypes, utils

        self.assertEqual(Rec({"x": "a"}).x, "a")
        self.assertEqual(ttrtypes.BType("Ind").show(), "Ind")
        self.assertEqual(probttrtypes.PConstraint(1).show(), "1.0")
        self.assertEqual(utils.show("a"), "a")

    def test_latex_renders_underscore_numeric_suffixes_as_subscripts(self):
        from pyttr.utils import to_latex

        self.assertEqual(to_latex("c_1"), r"\text{c}_{\text{1}}")
        self.assertEqual(to_latex("c_1", vars=["c_1"]), r"c_{1}")

    def test_split_ttrtype_modules_import(self):
        from pyttr.compound_types import FunType
        from pyttr.model import Possibility
        from pyttr.record_types import RecType
        from pyttr.string_types import TTRStringType
        from pyttr.terms import Fun
        from pyttr.type_core import BType

        ind = BType("Ind")

        self.assertEqual(Possibility("M").show().splitlines()[1], "M:")
        self.assertEqual(RecType({"x": ind}).show(), "{x : Ind}")
        self.assertEqual(Fun("x", ind, "x").app("j"), "j")
        self.assertEqual(FunType(ind, ind).show(), "(Ind->Ind)")
        self.assertEqual(TTRStringType([ind]).show(), "Ind")

    def test_split_probttrtype_modules_import(self):
        from pyttr.prob_compound_types import MeetType
        from pyttr.prob_constraints import PConstraint
        from pyttr.prob_predicates import PType
        from pyttr.prob_record_types import RecType
        from pyttr.prob_terms import Fun, Possibility
        from pyttr.prob_type_core import BType
        from pyttr.ttrtypes import Pred

        ind = BType("Ind")
        pred = Pred("run", [ind])

        self.assertEqual(PConstraint(1).show(), "1.0")
        self.assertEqual(PType(pred, ["j"]).show(), "run(j)")
        self.assertEqual(MeetType(ind, ind).show(), "(Ind&Ind)")
        self.assertEqual(RecType({"x": ind}).show(), "{x : Ind}")
        self.assertEqual(Fun("x", ind, "x").app("j"), "j")
        self.assertEqual(Possibility("M").show().splitlines()[1], "M:")

    def test_package_root_does_not_export_ambiguous_type_names(self):
        import pyttr
        from pyttr import probttrtypes, ttrtypes
        from pyttr.prob_record_types import RecType as ProbRecType
        from pyttr.record_types import RecType

        self.assertEqual(pyttr.__all__, ())
        self.assertIs(ttrtypes.RecType, RecType)
        self.assertIs(probttrtypes.RecType, ProbRecType)
        self.assertIsNot(ttrtypes.RecType, probttrtypes.RecType)

        for name in ("Type", "BType", "PType", "RecType", "Fun"):
            self.assertFalse(hasattr(pyttr, name))

        with self.assertRaises(ImportError):
            exec("from pyttr import RecType", {})


if __name__ == "__main__":
    unittest.main()
