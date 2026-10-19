import unittest
from unittest.mock import patch

from pyttr.core.records import Rec
from pyttr.categorical.record_types import RecType
from pyttr.categorical.type_core import BType
from pyttr.interactive_display import render_interactive_html, show_interactive


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

    def test_inline_backend_displays_an_iframe(self):
        with patch('IPython.display.display') as display:
            show_interactive(Rec({'x': 'j'}), backend='inline')
        output = display.call_args.args[0]['text/html']
        self.assertIn('srcdoc=', output)
        self.assertIn('Interactive record', output)


if __name__ == '__main__':
    unittest.main()
