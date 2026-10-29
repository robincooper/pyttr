# pyttr

This is the 2.x release line of the Python implementation of Type Theory with
Records (TTR). The original implementation is maintained on the
[`1.x` branch](https://github.com/robincooper/pyttr/tree/1.x). After both release
lines are published on PyPI, install one with `python -m pip install "pyttr>=2,<3"` or
`python -m pip install "pyttr>=1,<2"`. Only one release line can be installed
in a Python environment at a time.

The 2.x core implementation lives in the `pyttr` package under
`src/`, with top-level compatibility modules kept so older user code can
continue to import `ttrtypes`, `records`, `utils`, and related modules while
the cleanup proceeds.

## Requirements

- Python 3.11 or later
- NumPy
- IPython, for notebook and LaTeX display helpers

Notebook work can also use JupyterLab via the optional `notebooks` dependency
group.

Interactive record display can appear inline in a notebook or in a separate
desktop window. The window backend requires the optional `display` dependency
group:

```sh
python -m pip install -e ".[display]"
```

```python
from pyttr.categorical import BType, RecType
from pyttr.utils import show_interactive

record_type = RecType({"x": BType("Ind"), "person": {"name": BType("Ind")}})
show_interactive(record_type)                       # inline in a notebook; window otherwise
show_interactive(record_type, backend="window")     # choose a window explicitly
```

Both views let you expand and collapse nested records with a click, including
record types inside compound types. Any object with a `to_latex()` method can
also be displayed. LaTeX typesetting loads MathJax from the
internet. The window backend requires a
local desktop session; when called from a notebook, it enables Qt event-loop
integration automatically.

SPA-TTR experiments use the optional `spa` dependency group, which installs
PyTorch and TorchHD:

```sh
python -m pip install -e ".[spa]"
```

## Development

Install the project in editable mode with development dependencies:

```sh
python -m pip install -e ".[dev]"
```

Run tests:

```sh
python -m unittest discover -s tests
```

The test suite includes regression tests, the Python example scripts, and
in-memory execution of the notebooks.

Run the full local verification suite:

```sh
python scripts/check.py
```

or:

```sh
make check
```

This runs AST parsing, warnings-as-errors import checks, the unittest suite,
and a fresh-install smoke test from outside the repository. To run only the
fresh-install smoke test:

```sh
make fresh-install
```

## Layout

- `src/pyttr/core/`: shared records, terms, type structure, and model infrastructure
- `src/pyttr/categorical/`: categorical TTR implementation and public API
- `src/pyttr/probabilistic/`: probabilistic TTR implementation and public API
- `src/pyttr/spa/`: Semantic Pointer Architecture encodings of TTR objects
- remaining modules in `src/pyttr/`: shared utilities and compatibility exports
- `tests/`: regression, example, and notebook execution tests
- `example-*.py` and `notebooks/`: example material
- top-level `records.py`, `ttrtypes.py`, `probttrtypes.py`, `utils.py`, and
  `config.py`: compatibility wrappers for legacy imports

## Public API

Choose the semantic API explicitly. The public record-type name remains
`RecType` in both APIs. For categorical TTR:

```python
from pyttr.categorical import BType, Rec, RecType

Ind = BType("Ind")
Ind.judge("j")
person = RecType({"x": Ind})
assert person.query(Rec({"x": "j"})) is True
```

For probabilistic TTR:

```python
from pyttr.probabilistic import BType, Rec, RecType

Ind = BType("Ind")
Ind.judge("j", 0.6, 0.8)
person = RecType({"x": Ind})
probability = person.query(Rec({"x": "j"}))
assert (probability.min, probability.max) == (0.6, 0.8)
```

The package root intentionally does not re-export names such as `Type`,
`BType`, `PType`, `RecType`, or `Fun`, because those names can have different
meanings in categorical and probabilistic TTR. Shared record values are also
available as `from pyttr.core import Rec`.

Each semantic API has a separate default model, so categorical `BType("Ind")`
and probabilistic `BType("Ind")` can coexist without sharing evidence. Use
`Possibility` and the `poss=` argument for explicit models. Each API's
`initmodel()` clears its own default model. Types from different semantic
families with the same name cannot be registered in the same explicit model.

Existing imports such as `pyttr.ttrtypes`, `pyttr.probttrtypes`,
`pyttr.record_types`, and `pyttr.prob_record_types` remain compatibility exports
of the same objects. Top-level notebook imports such as `import ttrtypes` also
continue to work. The legacy `ttrtypes.initmodel()` and `pyttr.model.initmodel()`
clear all loaded default models, preserving the old global-reset workflow.

The notebooks use the explicit semantic APIs above: `pyttr.categorical` for
categorical TTR, `pyttr.probabilistic` for probabilistic TTR, and `pyttr.core`
for shared record structures.

SPA is an encoding layer over these TTR objects, rather than a third TTR
semantics. Use `pyttr.spa.Codebook` and `pyttr.spa.Encoder` to produce TorchHD
hypervectors; `WitnessCache` provides cache-based evidence for basic type
judgements. `Codebook(..., vsa="MAP")` forwards the VSA model choice to
TorchHD; see `notebooks/spa-ttr.ipynb` for basic witness-cache judgements,
record-type merge, and question answering based on the two SPA-TTR papers.

## Implementation boundaries

Both semantic implementations inherit from the abstract `core.TypeClass`.
They define judgment, querying, witness creation, possibility assignment, and
subtyping, including their own witness-cache formats. Categorical queries
retain their existing Boolean and legacy sentinel results; probabilistic
queries retain `PConstraint` probability intervals.

Shared record and compound structure lives in core bases such as
`RecTypeStructure`, `MeetTypeStructure`, and `PTypeClassStructure`. They provide
field traversal, display, substitution, and structural algorithms, delegating
semantic operations to concrete types. New objects created by nesting,
substitution, or merging preserve the semantic implementation. Shared term
operations likewise preserve probabilistic `Fun` objects and their matching
support.

Core imports neither semantic package; neither semantic package imports the
other or the legacy compatibility facades. The tests check these import
boundaries in fresh Python processes.

This refactor preserves the existing feature sets: probabilistic function,
list, and singleton types are still unimplemented. SPA encoding remains future
work; it can consume these TTR objects through an encoder/model layer.

## Records

`Rec` values store user labels in the `fields` mapping. Attribute access such
as `record.x` is still supported for compatibility, but labels no longer live
directly in the instance `__dict__`, so they cannot overwrite methods like
`show()` or `pathvalue()`.

Nested records can be folded for compact text or LaTeX output by setting
`max_record_depth` on `show()`, `to_latex()`, or the corresponding record
methods. The top-level record has depth zero, so a limit of two keeps one
nested record visible and folds its record-valued fields:

```python
from pyttr.categorical import Rec, show, to_latex

h_data = Rec({"object": {"id": "a", "data": {"f1": 0.25, "f2": 0.5}}})
assert show(h_data, max_record_depth=2) == (
    "{object = {id = a, data = {...}}}"
)
latex = to_latex(h_data, max_record_depth=2)
```

The default `None` retains the complete representation. The same option works
for nested `RecType` values and propagates through lists, tuples, sets, and
dictionaries containing records.

The verification suite covers both semantic APIs, compatibility imports,
structural operations, examples, and notebook execution.


## Modification history

20261021 Added KStarStringType
