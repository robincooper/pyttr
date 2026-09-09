import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr import probttrtypes as pttr
from pyttr import ttrtypes as ttr
from pyttr.prob_constraints import (
    ConjProb,
    DisjProb,
    PConstraint,
    PDiv,
    PExtreme,
    PMax,
    PMinus,
    PNeg,
    PPlus,
    PRound,
    PSum,
    PTimes,
)
from pyttr.records import Rec


class FixedQueryType:
    def __init__(self, probability):
        self.probability = probability

    def query(self, obj, c=None, oracle=None):
        return self.probability


class ProbabilisticTypeBehaviorTests(unittest.TestCase):
    def setUp(self):
        ttr.initmodel()

    def assertProbability(self, probability, low, high):
        self.assertAlmostEqual(probability.min, low)
        self.assertAlmostEqual(probability.max, high)

    def test_probability_combinators_combine_intervals(self):
        first = PConstraint(0.2, 0.3)
        second = PConstraint(0.4, 0.5)

        self.assertProbability(PMax([first, second]), 0.4, 0.5)
        self.assertProbability(PExtreme([first, second]), 0.2, 0.5)
        self.assertProbability(PSum([first, second]), 0.6, 0.8)
        self.assertProbability(PNeg(first), 0.7, 0.8)
        self.assertProbability(PRound(PConstraint(0.12345, 0.98765), 2), 0.12, 0.99)
        self.assertProbability(PTimes(first, PConstraint(0.3, 0.4)), 0.06, 0.12)
        self.assertProbability(PDiv(PConstraint(0.2, 0.4), PConstraint(0.5, 0.8)), 0.4, 0.5)
        self.assertProbability(PMinus(PConstraint(0.7, 0.9), PConstraint(0.2, 0.3)), 0.5, 0.6)
        self.assertProbability(PPlus(first, second), 0.6, 0.8)

    def test_conjunction_and_disjunction_query_member_types(self):
        first = FixedQueryType(PConstraint(0.2, 0.5))
        second = FixedQueryType(PConstraint(0.3, 0.4))

        self.assertProbability(ConjProb([("a", first), ("a", second)]), 0.06, 0.2)
        self.assertProbability(DisjProb([("a", first), ("a", second)]), 0.44, 0.7)

    def test_judgement_query_and_forget_round_trip_probability(self):
        ind = pttr.BType("Ind")

        judged = ind.judge("j", 0.25, 0.75)

        self.assertProbability(judged, 0.25, 0.75)
        self.assertProbability(ind.query("j"), 0.25, 0.75)
        self.assertProbability(ind.forget("j"), 0.25, 0.75)
        self.assertProbability(ind.query("j"), 0.0, 1.0)

    def test_neg_type_inverts_base_type_probability(self):
        ind = pttr.BType("Ind")
        ind.judge("j", 0.2, 0.6)

        negated = pttr.NegType(ind)

        self.assertProbability(negated.query("j"), 0.4, 0.8)
        self.assertProbability(negated.query("missing"), 0.0, 1.0)

    def test_var_type_uses_context_to_disambiguate_candidates(self):
        ind = pttr.BType("Ind")
        other = pttr.BType("Other")
        variable = pttr.VarType([ind, other])

        self.assertProbability(variable.query("j", [("j", ind)]), 1.0, 1.0)
        self.assertProbability(variable.query_v("j", ind, [("j", ind)]), 1.0, 1.0)
        self.assertProbability(variable.query_v("j", other, [("j", ind)]), 0.0, 0.0)
        self.assertProbability(variable.query("j", [("j", ind), ("j", other)]), 0.0, 0.0)

    def test_matchlist_binds_variable_values(self):
        ind = pttr.BType("Ind")
        values = [None]

        self.assertTrue(pttr.matchlist(["x"], ["j"], pttr._M, ["x"], [ind], values))
        self.assertEqual(values, ["j"])
        self.assertFalse(pttr.matchlist(["j"], ["k"], pttr._M))
        self.assertFalse(pttr.matchlist(["x"], ["j", "k"], pttr._M, ["x"], [ind], [None]))

    def test_probabilistic_record_type_dependent_field_query(self):
        ind = pttr.BType("Ind")
        ind.judge("j", 0.7, 0.9)
        ind.judge("k", 0.2, 0.4)
        man = pttr.Pred("man", [ind])
        pttr.PType(man, ["j"]).judge("e_j", 0.5, 0.8)

        record_type = pttr.RecType(
            {
                "x": ind,
                "event": (pttr.Fun("v", ind, pttr.PType(man, ["v"])), ["x"]),
            }
        )

        self.assertProbability(
            record_type.query(Rec({"x": "j", "event": "e_j"})),
            0.35,
            0.72,
        )
        self.assertProbability(record_type.query(Rec({"x": "k", "event": "e_j"})), 0.0, 0.4)
        self.assertProbability(record_type.query(Rec({"x": "j"})), 0.0, 0.0)


if __name__ == "__main__":
    unittest.main()
