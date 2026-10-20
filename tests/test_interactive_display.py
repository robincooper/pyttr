import unittest
from unittest.mock import patch

from pyttr.core.records import Rec
from pyttr.categorical.record_types import RecType
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


if __name__ == '__main__':
    unittest.main()
