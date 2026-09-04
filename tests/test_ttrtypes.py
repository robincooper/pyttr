import unittest

import ttrtypes as ttr


class TypeTests(unittest.TestCase):
    def setUp(self):
        ttr.initmodel()

    def test_basic_type_judgement_and_query(self):
        ind = ttr.BType("Ind")

        self.assertTrue(ind.judge("j"))
        self.assertTrue(ind.query("j"))
        self.assertFalse(ind.query("missing"))

    def test_meet_type_queries_both_components(self):
        t1 = ttr.Type("T1")
        t2 = ttr.Type("T2")
        t1.judge("a")
        t2.judge("a")
        t1.judge("b")

        meet = ttr.MeetType(t1, t2)

        self.assertTrue(meet.query("a"))
        self.assertFalse(meet.query("b"))

    def test_checked_function_application_checks_domain(self):
        ind = ttr.BType("Ind")
        ind.judge("j")
        fun = ttr.Fun("x", ind, "x")

        self.assertEqual(fun.appc("j"), "j")
        self.assertIsNone(fun.appc("not_an_ind"))


if __name__ == "__main__":
    unittest.main()
