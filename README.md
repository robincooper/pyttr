# pyttr2

`pyttr2` is a cleanup branch of the Python implementation of Type Theory with
Records (TTR). The core implementation now lives in the `pyttr` package under
`src/`, with top-level compatibility modules kept so the older examples and
notebooks can continue to import `ttrtypes`, `records`, `utils`, and related
modules while the cleanup proceeds.

## Requirements

- Python 3.11 or later
- NumPy
- IPython, for notebook and LaTeX display helpers

Notebook work can also use JupyterLab via the optional `notebooks` dependency
group.

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

- `src/pyttr/`: canonical package code
- `tests/`: regression, example, and notebook execution tests
- `example-*.py` and `*.ipynb`: existing example material
- top-level `records.py`, `ttrtypes.py`, `probttrtypes.py`, `utils.py`, and
  `config.py`: compatibility wrappers for legacy imports

`Rec` values store user labels in the `fields` mapping. Attribute access such
as `record.x` is still supported for compatibility, but labels no longer live
directly in the instance `__dict__`, so they cannot overwrite methods like
`show()` or `pathvalue()`.

The first cleanup pass focuses on compatibility-safe modernization: packaging
metadata, basic regression tests, mutable-default cleanup, and warning fixes.
