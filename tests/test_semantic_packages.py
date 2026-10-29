"""Behavior and dependency boundaries of the semantic package APIs."""
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from pyttr import categorical as cat, probabilistic as prob
from pyttr.core import TypeClass as CoreType
from pyttr.core.record_types import RecTypeStructure
from pyttr.core.type_ops import combine_dep_types, merge_dep_types


class SemanticPackageTests(unittest.TestCase):
    def setUp(self):
        cat.initmodel()
        prob.initmodel()

    def assertProbability(self, result, low, high=None):
        self.assertIsInstance(result, prob.PConstraint)
        self.assertAlmostEqual(result.min, low)
        self.assertAlmostEqual(result.max, low if high is None else high)

    def test_packages_import_independently(self):
        for package, forbidden in (
            ('core', ('pyttr.categorical', 'pyttr.probabilistic')),
            ('categorical', ('pyttr.probabilistic',)),
            ('probabilistic', ('pyttr.categorical',)),
        ):
            with self.subTest(package=package):
                code = f'''
import importlib
import sys
importlib.import_module('pyttr.{package}')
for prefix in {forbidden + ('pyttr.ttrtypes', 'pyttr.probttrtypes')!r}:
    assert not any(n == prefix or n.startswith(prefix + '.') for n in sys.modules), prefix
'''
                env = dict(os.environ, PYTHONPATH=str(SRC))
                subprocess.run([sys.executable, '-B', '-W', 'error', '-c', code],
                               env=env, check=True, capture_output=True, text=True)

    def test_legacy_imports_keep_class_identity(self):
        from pyttr import ttrtypes, probttrtypes
        from pyttr.record_types import RecType
        from pyttr.prob_record_types import RecType as ProbRecType
        from pyttr.records import Rec
        self.assertIs(cat.RecType, RecType)
        self.assertIs(prob.RecType, ProbRecType)
        self.assertIs(cat.Rec, Rec)
        self.assertIs(prob.Rec, Rec)
        for name in ('TypeClass', 'Type', 'BType', 'PType', 'RecType', 'MeetType', 'JoinType', 'Fun'):
            self.assertIs(getattr(cat, name), getattr(ttrtypes, name))
            self.assertIs(getattr(prob, name), getattr(probttrtypes, name))

    def test_semantic_classes_share_core_without_inheriting_each_other(self):
        with self.assertRaises(TypeError):
            CoreType()
        for api in (cat, prob):
            self.assertTrue(issubclass(api.TypeClass, CoreType))
            self.assertTrue(issubclass(api.RecType, RecTypeStructure))
            self.assertTrue(issubclass(api.RecType, api.TypeClass))
        self.assertFalse(issubclass(prob.TypeClass, cat.TypeClass))
        self.assertFalse(issubclass(prob.RecType, cat.RecType))

    def test_same_named_types_have_independent_evidence(self):
        categorical = cat.BType('Ind')
        probabilistic = prob.BType('Ind')
        self.assertIsInstance(categorical, cat.TypeClass)
        self.assertIsInstance(probabilistic, prob.TypeClass)
        self.assertIsNot(categorical.poss, probabilistic.poss)
        self.assertIs(cat.BType('Ind'), categorical)
        self.assertIs(prob.BType('Ind'), probabilistic)
        categorical.judge('j')
        self.assertProbability(probabilistic.query('j'), 0, 1)
        probabilistic.judge('j', 0.25, 0.75)
        self.assertIs(categorical.query('j'), True)
        self.assertProbability(probabilistic.query('j'), 0.25, 0.75)
        self.assertFalse(cat.equal(categorical, probabilistic))

    def test_semantic_resets_are_independent_and_legacy_reset_clears_both(self):
        from pyttr.ttrtypes import initmodel
        c = cat.BType('Ind')
        p = prob.BType('Ind')
        cat.initmodel()
        self.assertIsNot(cat.BType('Ind'), c)
        self.assertIs(prob.BType('Ind'), p)
        c = cat.BType('Ind')
        prob.initmodel()
        self.assertIs(cat.BType('Ind'), c)
        self.assertIsNot(prob.BType('Ind'), p)
        initmodel()
        self.assertEqual(c.poss.model, {})
        self.assertEqual(p.poss.model, {})

    def test_explicit_model_rejects_same_name_from_different_semantics(self):
        model = cat.Possibility('M')
        cat.BType('Ind', poss=model)
        with self.assertRaises(TypeError):
            prob.BType('Ind', poss=model)
        with self.assertRaises(TypeError):
            prob.BType('Ind').in_poss(model)

    def test_nested_records_validate_create_and_query_in_each_semantics(self):
        for api in (cat, prob):
            with self.subTest(api=api.__name__):
                ind = api.BType('Ind')
                record_type = api.RecType({'inner': {'x': ind}})
                self.assertIsInstance(record_type.comps.inner, api.RecType)
                self.assertTrue(record_type.validate())
                witness = record_type.create()
                self.assertIsInstance(witness.inner, api.Rec)
                result = record_type.query(witness)
                if api is cat:
                    self.assertIs(result, True)
                else:
                    self.assertProbability(result, 1)

    def test_record_operations_preserve_semantics_and_model(self):
        for api in (cat, prob):
            with self.subTest(api=api.__name__):
                model = api.Possibility('M')
                ind = api.BType('Ind', poss=model)
                other = api.BType('Other', poss=model)
                left = api.RecType({'inner': {'x': ind}}).in_poss(model)
                right = api.RecType({'inner': {'y': other}}).in_poss(model)
                for result in (left.subst(ind, other), left.merge(right), left.amerge(right)):
                    self.assertIsInstance(result, api.RecType)
                    self.assertIsInstance(result.comps.inner, api.RecType)
                    self.assertIs(result.poss, model)
                    self.assertTrue(result.validate())
                merged = left.merge(right)
                self.assertEqual(set(merged.comps.inner.comps.labels()), {'x', 'y'})

    def test_probabilistic_shared_field_merge_uses_probabilistic_meet(self):
        a, b = prob.BType('A'), prob.BType('B')
        merged = prob.RecType({'x': a}).merge(prob.RecType({'x': b}))
        self.assertIsInstance(merged.comps.x, prob.MeetType)
        a.judge('j', 0.5)
        b.judge('j', 0.4)
        self.assertProbability(merged.query(prob.Rec({'x': 'j'})), 0.2)

    def test_substitution_preserves_probabilistic_compounds_and_functions(self):
        model = prob.Possibility('M')
        a, b = prob.BType('A', poss=model), prob.BType('B', poss=model)
        for constructor in (prob.MeetType, prob.JoinType):
            result = constructor(a, b).in_poss(model).subst(a, b)
            self.assertIsInstance(result, constructor)
            self.assertIs(result.poss, model)
            self.assertIs(result.comps.left, b)
            self.assertProbability(result.query('unknown'), 0, 1)
        fun = prob.Fun('x', a, a)
        changed = fun.subst(a, b)
        self.assertIsInstance(changed, prob.Fun)
        self.assertTrue(callable(changed.matches))
        self.assertIs(changed.body, b)

    def test_dependent_type_operations_preserve_probabilistic_functions(self):
        a, b = prob.BType('A'), prob.BType('B')
        left = prob.Fun('x', a, a)
        right = prob.Fun('y', a, b)
        for operation in (merge_dep_types, combine_dep_types):
            result = operation(left, right)
            self.assertIsInstance(result, prob.Fun)
            while isinstance(result, prob.Fun):
                result = result.body
            self.assertIsInstance(result, prob.MeetType)

    def test_dependent_records_create_and_query_in_each_semantics(self):
        for api in (cat, prob):
            with self.subTest(api=api.__name__):
                ind = api.BType('Ind')
                pred = api.Pred('run', [ind])
                record_type = api.RecType({
                    'x': ind,
                    'event': (api.Fun('v', ind, api.PType(pred, ['v'])), ['x']),
                })
                self.assertTrue(record_type.validate())
                result = record_type.query(record_type.create())
                if api is cat:
                    self.assertIs(result, True)
                else:
                    self.assertProbability(result, 1)

    def test_logical_type_learning_uses_shared_helpers(self):
        for api in (cat, prob):
            ind = api.BType('Ind')
            logical = api.RecType({'x': ind})
            conditions = logical.witness_conditions.copy()
            logical.learn_witness_condition(lambda _: False)
            logical.learn_witness_type(ind)
            self.assertEqual(logical.witness_conditions, conditions)
            self.assertEqual(logical.witness_types, [])


if __name__ == '__main__':
    unittest.main()
