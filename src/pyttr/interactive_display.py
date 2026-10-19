"""Interactive HTML display of records and record types."""

from html import escape

from .core.records import Rec
from .core.record_types import RecTypeStructure
from .utils import to_latex


_STYLE = """
<style>
  html, body { margin: 0; background: #fff; color: #222; }
  .pyttr-display { padding: 20px; font: 18px/1.5 Georgia, 'Times New Roman', serif; }
  .pyttr-record { display: inline-flex; align-items: stretch; vertical-align: middle; }
  .pyttr-bracket { width: 8px; flex: 0 0 8px; border-top: 2px solid currentColor; border-bottom: 2px solid currentColor; }
  .pyttr-bracket-left { border-left: 2px solid currentColor; }
  .pyttr-bracket-right { border-right: 2px solid currentColor; }
  .pyttr-fields { display: grid; grid-template-columns: max-content max-content max-content; column-gap: 10px; align-items: center; padding: 3px 10px; }
  .pyttr-label { text-align: left; white-space: nowrap; }
  .pyttr-op { text-align: center; }
  .pyttr-value { white-space: nowrap; }
  .pyttr-toggle { display: inline-block; margin-right: 5px; width: 23px; height: 23px; padding: 0; vertical-align: middle; border: 1px solid #aaa; border-radius: 4px; background: #fff; color: #222; font: 15px Arial, sans-serif; cursor: pointer; }
  .pyttr-toggle:hover { background: #eee; }
  .pyttr-ellipsis { color: #666; }
  .pyttr-record[data-collapsed="true"] > .pyttr-fields,
  .pyttr-record[data-collapsed="true"] > .pyttr-bracket { display: none; }
  .pyttr-record[data-collapsed="false"] > .pyttr-ellipsis { display: none; }
</style>
"""

_SCRIPT = """
<script>
document.addEventListener('click', function (event) {
  const button = event.target.closest('.pyttr-toggle');
  if (!button) return;
  const record = button.nextElementSibling;
  const collapsed = record.dataset.collapsed !== 'true';
  record.dataset.collapsed = String(collapsed);
  button.textContent = collapsed ? '+' : '−';
  button.setAttribute('aria-expanded', String(!collapsed));
  button.setAttribute('aria-label', (collapsed ? 'Expand' : 'Collapse') + ' nested record');
});
</script>
"""


def _math(obj, *, anglebrackets=False):
    latex = to_latex(obj, anglebrackets=anglebrackets)
    return '<span class="pyttr-math">\\(' + escape(latex) + '\\)</span>'


def _record_html(obj, ancestors):
    if id(obj) in ancestors:
        return '<span class="pyttr-ellipsis">[cycle]</span>'
    ancestors = ancestors | {id(obj)}
    is_type = isinstance(obj, RecTypeStructure)
    fields = obj.comps.items() if is_type else obj.fields.items()
    op = ':' if is_type else '='
    rows = []
    for label, value in fields:
        if isinstance(value, (Rec, RecTypeStructure)):
            shown = (
                '<button type="button" class="pyttr-toggle" aria-expanded="true" '
                'aria-label="Collapse nested record">−</button>'
                + _record_html(value, ancestors)
            )
        else:
            shown = _math(value, anglebrackets=is_type)
        rows.append(
            '<span class="pyttr-label">' + _math(label) + '</span>'
            '<span class="pyttr-op">' + op + '</span>'
            '<span class="pyttr-value">' + shown + '</span>'
        )
    return (
        '<span class="pyttr-record" data-collapsed="false">'
        '<span class="pyttr-bracket pyttr-bracket-left" aria-hidden="true"></span>'
        '<span class="pyttr-fields">' + ''.join(rows) + '</span>'
        '<span class="pyttr-bracket pyttr-bracket-right" aria-hidden="true"></span>'
        '<span class="pyttr-ellipsis">[ ⋯ ]</span>'
        '</span>'
    )


def render_interactive_html(obj):
    """Return an HTML document for an interactive record."""
    if not isinstance(obj, (Rec, RecTypeStructure)):
        raise TypeError('Interactive display requires a Rec or RecType object')
    content = _record_html(obj, set())
    return (
        '<!doctype html><html><head><meta charset="utf-8">'
        + _STYLE + '</head><body><div class="pyttr-display">'
        + content + '</div>' + _SCRIPT
        + '<script src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>'
        + '</body></html>'
    )


def show_interactive(obj, backend='inline'):
    """Show an expandable record inline in a notebook or in a Qt window.

    ``backend`` is ``'inline'`` or ``'window'``. The window backend requires
    PySide6. MathJax is loaded from a CDN by both backends.
    """
    if backend not in ('inline', 'window'):
        raise ValueError("backend must be 'inline' or 'window'")
    document = render_interactive_html(obj)
    if backend == 'inline':
        try:
            from IPython.display import display
        except ImportError as exc:
            raise RuntimeError('Inline display requires IPython') from exc
        # srcdoc keeps this view's script and styles independent of the notebook.
        frame = (
            '<iframe title="Interactive record" '
            'style="width:100%;height:360px;border:0" '
            'sandbox="allow-scripts" srcdoc="'
            + escape(document, quote=True) + '"></iframe>'
        )
        return display({'text/html': frame}, raw=True)

    try:
        from PySide6.QtWidgets import QApplication
        from PySide6.QtWebEngineWidgets import QWebEngineView
        from PySide6.QtWebEngineCore import QWebEngineSettings
    except ImportError as exc:
        raise RuntimeError('Window display requires PySide6 (pip install pyttr2[display])') from exc

    if _in_notebook():
        from IPython import get_ipython
        get_ipython().run_line_magic('gui', 'qt6')
    app = QApplication.instance() or QApplication([])
    view = QWebEngineView()
    view.settings().setAttribute(
        QWebEngineSettings.WebAttribute.LocalContentCanAccessRemoteUrls, True
    )
    view.setWindowTitle('pyttr record')
    view.resize(760, 460)
    view.setHtml(document)
    view.show()
    _open_windows.append(view)
    if not _in_notebook():
        app.exec()
        _open_windows.remove(view)
    return view


def _in_notebook():
    try:
        from IPython import get_ipython
    except ImportError:
        return False
    shell = get_ipython()
    return shell is not None and shell.__class__.__name__ == 'ZMQInteractiveShell'


_open_windows = []
