"""Interactive HTML display of objects with LaTeX representations."""

from html import escape
from inspect import signature
from itertools import count
import json

from .core.records import Rec
from .core.record_types import RecTypeStructure
from .core.model import Possibility
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
  [id^="pyttr-record-"] { cursor: pointer; }
  [id^="pyttr-record-"]:hover { opacity: .7; }
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

_RESIZE_SCRIPT = """
<script>
(() => {
  if (window.parent === window) return;
  const content = document.querySelector('.pyttr-display');
  const reportHeight = () => window.parent.postMessage({
    kind: 'pyttr-interactive-height',
    height: Math.ceil(content.getBoundingClientRect().height) + 2
  }, '*');
  new ResizeObserver(reportHeight).observe(content);
  window.addEventListener('load', reportHeight);
  window.addEventListener('message', event => {
    if (event.source === window.parent && event.data?.kind === 'pyttr-measure') {
      reportHeight();
    }
  });
})();
</script>
"""

_INLINE_ONLOAD = """((frame) => {
  window.addEventListener('message', event => {
    if (event.source !== frame.contentWindow ||
        event.data?.kind !== 'pyttr-interactive-height') return;
    const height = Number(event.data.height);
    if (Number.isFinite(height) && height > 0) {
      frame.style.height = Math.ceil(height) + 'px';
    }
  });
  frame.contentWindow.postMessage({kind: 'pyttr-measure'}, '*');
})(this)"""


def _latex(obj, *, anglebrackets=False):
    method = getattr(obj, 'to_latex', None)
    if callable(method):
        try:
            signature(method).bind([])
        except TypeError:
            latex = method()
        else:
            latex = to_latex(obj, anglebrackets=anglebrackets)
    else:
        latex = to_latex(obj, anglebrackets=anglebrackets)
    return latex


def _math(obj, *, anglebrackets=False):
    return '<span class="pyttr-math">\\(' + escape(_latex(obj, anglebrackets=anglebrackets)) + '\\)</span>'


def _all_records(obj):
    """Find record values in the part of an object used by LaTeX renderers."""
    records = []
    seen = set()

    def visit(value):
        if id(value) in seen or isinstance(value, (str, bytes, int, float, bool, type(None))):
            return
        seen.add(id(value))
        if isinstance(value, RecTypeStructure):
            records.append(value)
            children = value.comps.values()
        elif isinstance(value, Rec):
            records.append(value)
            children = value.fields.values()
        elif isinstance(value, Possibility):
            children = (
                witnesses for _, witnesses in value._latex_entries()
            )
        elif isinstance(value, dict):
            children = value.values()
        elif isinstance(value, (list, tuple)):
            children = value
        else:
            try:
                attrs = vars(value)
            except TypeError:
                return
            ignored = {
                'poss', 'model', 'witness_cache', 'supertype_cache',
                'witness_conditions', 'witness_types', 'witness_funs',
            }
            children = (child for name, child in attrs.items() if name not in ignored)
        for child in children:
            visit(child)

    visit(obj)
    return records


def _make_template(latex, candidates, definitions, numbers):
    for record in sorted(candidates, key=lambda r: len(_latex(r)), reverse=True):
        source = _latex(record)
        if not source:
            continue
        while source in latex:
            number = str(next(numbers))
            nested = [child for child in _all_records(record) if child is not record]
            definitions[number] = _make_template(source, nested, definitions, numbers)
            latex = latex.replace(source, '\x01' + number + '\x02', 1)
    return latex


_COMPOUND_SCRIPT = r"""
<script>
(() => {
  const data = __STATE__;
  const math = document.getElementById('pyttr-compound-math');
  const collapsed = new Set();
  const expand = template => template.replace(/\u0001(\d+)\u0002/g, (_, id) => {
    const body = collapsed.has(id) ? '\\left[\\cdots\\right]' : expand(data.records[id]);
    return '\\cssId{pyttr-record-' + id + '}{' + body + '}';
  });
  const source = () => '\\(' + expand(data.root) + '\\)';
  math.textContent = source();
  document.addEventListener('click', event => {
    const target = event.target.closest('[id^="pyttr-record-"]');
    if (!target || !math.contains(target)) return;
    const id = target.id.slice('pyttr-record-'.length);
    if (collapsed.has(id)) collapsed.delete(id);
    else collapsed.add(id);
    MathJax.typesetClear([math]);
    math.textContent = source();
    MathJax.typesetPromise([math]);
  });
})();
</script>
"""


def _compound_html(obj):
    definitions = {}
    template = _make_template(_latex(obj), _all_records(obj), definitions, count())
    if not definitions:
        return _math(obj)
    state = json.dumps({'root': template, 'records': definitions}).replace('<', r'\u003c')
    return (
        '<span class="pyttr-math" id="pyttr-compound-math"></span>'
        + _COMPOUND_SCRIPT.replace('__STATE__', state)
    )


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
    """Return HTML for a record or any object with ``to_latex``."""
    if isinstance(obj, (Rec, RecTypeStructure)):
        content = _record_html(obj, set())
    elif callable(getattr(obj, 'to_latex', None)):
        content = _compound_html(obj)
    else:
        raise TypeError('Interactive display requires a record or an object with to_latex()')
    return (
        '<!doctype html><html><head><meta charset="utf-8">'
        + _STYLE + '</head><body><div class="pyttr-display">'
        + content + '</div>' + _SCRIPT + _RESIZE_SCRIPT
        + '<script>window.MathJax = {loader: {load: ["[tex]/html"]}, '
          'tex: {packages: {"[+]": ["html"]}}};</script>'
        + '<script src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>'
        + '</body></html>'
    )


def _resolve_backend(backend):
    if backend is None:
        return 'inline' if _in_notebook() else 'window'
    if backend not in ('inline', 'window'):
        raise ValueError("backend must be 'inline' or 'window'")
    return backend


def show_interactive(obj, backend=None):
    """Show LaTeX inline in a notebook or in a Qt window.

    The default backend is ``'inline'`` in notebooks and ``'window'`` elsewhere.
    Records, including those inside compound objects, can be collapsed by click.
    The window backend requires PySide6.
    MathJax is loaded from a CDN by both backends.
    """
    backend = _resolve_backend(backend)
    document = render_interactive_html(obj)
    if backend == 'inline':
        try:
            from IPython.display import display
        except ImportError as exc:
            raise RuntimeError('Inline display requires IPython') from exc
        # srcdoc keeps this view's script and styles independent of the notebook.
        # The sandboxed frame reports its height to this element after rendering
        # and whenever expanding a record changes the content size.
        frame = (
            '<iframe title="Interactive record" '
            'style="width:100%;height:80px;border:0" '
            'sandbox="allow-scripts" onload="'
            + escape(_INLINE_ONLOAD, quote=True) + '" srcdoc="'
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
