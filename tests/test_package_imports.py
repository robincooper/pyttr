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


if __name__ == "__main__":
    unittest.main()
