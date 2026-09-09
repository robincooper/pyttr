"""Type Theory with Records implementation.

Public classes and functions are exposed from explicit submodules such as
``pyttr.ttrtypes`` and ``pyttr.probttrtypes``. The package root deliberately
does not re-export names like ``RecType`` because deterministic,
probabilistic, and future alternative modules may define objects with the same
names.
"""

__all__: tuple[str, ...] = ()
