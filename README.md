# pyttr2

`pyttr2` is a cleanup branch of the Python implementation of Type Theory with
Records (TTR). The current code preserves the flat module layout from `pyttr`
while adding modern project metadata and regression tests so future refactors
can be made with more confidence.

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

The first cleanup pass focuses on compatibility-safe modernization: packaging
metadata, basic regression tests, mutable-default cleanup, and warning fixes.
