import unittest

from records import Rec
from utils import show


class RecTests(unittest.TestCase):
    def test_nested_dicts_become_records(self):
        rec = Rec({"f": {"g": "a"}})

        self.assertIsInstance(rec.f, Rec)
        self.assertEqual(rec.pathvalue("f.g"), "a")

    def test_substitution_recurses_through_nested_records(self):
        rec = Rec({"f": {"g": "a"}, "h": "b"})

        self.assertEqual(show(rec.subst("a", "z")), "{f = {g = z}, h = b}")

    def test_flatten_and_unflatten_round_trip(self):
        rec = Rec({"f": {"g": "a"}, "h": "b"})

        self.assertEqual(show(rec.flatten()), "{f.g = a, h = b}")
        self.assertEqual(show(rec.flatten().unflatten()), show(rec))

    def test_relabel_returns_new_record(self):
        rec = Rec({"f": "a", "g": "b"})

        relabeled = rec.relabel("f", "z")

        self.assertEqual(show(rec), "{f = a, g = b}")
        self.assertEqual(show(relabeled), "{g = b, z = a}")


if __name__ == "__main__":
    unittest.main()
