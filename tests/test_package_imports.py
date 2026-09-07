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


if __name__ == "__main__":
    unittest.main()
