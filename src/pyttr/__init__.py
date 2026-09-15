"""Type Theory with Records implementation.

Public classes and functions are exposed from ``pyttr.categorical`` and
``pyttr.probabilistic``. Shared structures live in ``pyttr.core``; the legacy
``pyttr.ttrtypes`` and ``pyttr.probttrtypes`` imports remain supported.
The package root deliberately
does not re-export names like ``RecType`` because deterministic,
probabilistic modules may define objects with the same
names.
"""

__all__: tuple[str, ...] = ()
