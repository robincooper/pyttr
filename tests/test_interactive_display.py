import unittest
import json
import re
from types import SimpleNamespace
from unittest.mock import patch

from pyttr.core.model import Possibility
from pyttr.probabilistic.terms import Possibility as ProbPossibility
from pyttr.core.records import Rec
from pyttr.categorical.record_types import RecType
from pyttr.categorical.compound_types import MeetType, FunType, ListType
from pyttr.categorical.type_core import BType
from pyttr.interactive_display import (
    _resolve_backend, render_interactive_html, show_interactive,
)


class InteractiveDisplayTests(unittest.TestCase):
    def test_nested_record_has_clickable_control_and_left_aligned_labels(self):
        obj = Rec({'person': {'name': 'Ada'}, 'x': 'j'})
        html = render_interactive_html(obj)
        self.assertIn('text-align: left', html)
        self.assertIn('aria-label="Collapse nested record"', html)
        self.assertIn(r'\(\text{Ada}\)', html)
        self.assertIn('data-collapsed="false"', html)
        self.assertIn('pyttr-bracket-right', html)

    def test_record_type_uses_colon_and_latex_leaves(self):
        obj = RecType({'person': {'name': BType('Ind')}})
        html = render_interactive_html(obj)
        self.assertIn('<span class="pyttr-op">:</span>', html)
        self.assertIn('aria-label="Collapse nested record"', html)
        self.assertIn(r'\(\textit{Ind}\)', html)

    def test_invalid_backend_and_value(self):
        with self.assertRaises(ValueError):
            show_interactive(Rec(), backend='other')
        with self.assertRaises(TypeError):
            render_interactive_html('not a record')

    def test_other_latex_objects_render(self):
        class WithVars:
            def to_latex(self, vars):
                return r'\alpha + \beta'

        class WithoutVars:
            def to_latex(self):
                return r'\gamma'

        self.assertIn(r'\(\alpha + \beta\)', render_interactive_html(WithVars()))
        self.assertIn(r'\(\gamma\)', render_interactive_html(WithoutVars()))

    def test_record_type_inside_compound_types_is_collapsible(self):
        nested = RecType({'person': {'name': BType('Ind')}})
        for compound in (
            MeetType(nested, BType('Ind')),
            FunType(BType('Ind'), nested),
            ListType(nested),
        ):
            with self.subTest(type=type(compound).__name__):
                html = render_interactive_html(compound)
                self.assertIn('id="pyttr-compound-math"', html)
                self.assertIn(r'\cssId{pyttr-record-', html)
                state = json.loads(re.search(r'const data = (\{.*?\});', html).group(1))
                self.assertEqual(len(state['records']), 2)
                self.assertIn('\x010\x02', state['root'])
                self.assertIn('\x011\x02', state['records']['0'])

    def test_custom_latex_wrapper_can_contain_a_collapsible_record(self):
        class Wrapper:
            def __init__(self, child):
                self.child = child

            def to_latex(self, vars):
                from pyttr.utils import to_latex
                return r'\boxed{' + to_latex(self.child, vars) + '}'

        html = render_interactive_html(Wrapper(RecType({'x': BType('Ind')})))
        self.assertIn('id="pyttr-compound-math"', html)
        state = json.loads(re.search(r'const data = (\{.*?\});', html).group(1))
        self.assertEqual(len(state['records']), 1)

    def test_default_backend_tracks_notebook_environment(self):
        with patch('pyttr.interactive_display._in_notebook', return_value=True):
            self.assertEqual(_resolve_backend(None), 'inline')
        with patch('pyttr.interactive_display._in_notebook', return_value=False):
            self.assertEqual(_resolve_backend(None), 'window')
        self.assertEqual(_resolve_backend('inline'), 'inline')
        self.assertEqual(_resolve_backend('window'), 'window')

    def test_inline_backend_displays_an_iframe(self):
        with patch('IPython.display.display') as display:
            show_interactive(Rec({'x': 'j'}), backend='inline')
        output = display.call_args.args[0]['text/html']
        self.assertIn('srcdoc=', output)
        self.assertIn('Interactive record', output)
        self.assertIn('height:80px', output)
        self.assertIn('pyttr-interactive-height', output)
        self.assertIn('pyttr-measure', output)
        self.assertNotIn('height:360px', output)

    def test_inline_document_reports_height_changes(self):
        html = render_interactive_html(Rec({'person': Rec({'name': 'Ada'})}))
        self.assertIn('new ResizeObserver(reportHeight).observe(content)', html)
        self.assertIn("window.addEventListener('load', reportHeight)", html)

    def test_possibility_latex_matches_visible_show_entries(self):
        model = Possibility('M1', {
            'Ind': SimpleNamespace(witness_cache=['a', 'b']),
            'Ty': SimpleNamespace(witness_cache=['hidden']),
        })
        latex = model.to_latex()
        self.assertIn(r'\begin{array}{lcl}', latex)
        self.assertIn(r'\hline', latex)
        self.assertIn(r'\text{M}_{\text{1}}: & &', latex)
        self.assertIn(r'\text{Ind} & : & [ \text{a}, \text{b}]', latex)
        self.assertNotIn('hidden', latex)
        self.assertNotIn('Ty', latex)
        self.assertNotIn(r'\multicolumn', latex)
        self.assertIn(' & & ', Possibility('Empty').to_latex())
        self.assertIn(r'\text{\_Model\_}', Possibility('_Model_').to_latex())

    def test_possibility_is_interactive_and_record_witnesses_collapse(self):
        model = Possibility('M', {
            'R': SimpleNamespace(witness_cache=[Rec({'x': 'a'})]),
        })
        html = render_interactive_html(model)
        self.assertIn('id="pyttr-compound-math"', html)
        self.assertIn(r'\cssId{pyttr-record-', html)
        self.assertNotIn(r'\multicolumn', html)
        with patch('IPython.display.display') as display:
            show_interactive(model, backend='inline')
        self.assertIn('srcdoc=', display.call_args.args[0]['text/html'])

    def test_probabilistic_possibility_uses_paired_witnesses(self):
        model = ProbPossibility('P', {
            'Ind': SimpleNamespace(witness_cache=(['a'], ['certain'])),
        })
        latex = model.to_latex()
        self.assertIn(r'\langle \text{a}, \text{certain}\rangle', latex)
        self.assertIn('pyttr-display', render_interactive_html(model))


if __name__ == '__main__':
    unittest.main()
