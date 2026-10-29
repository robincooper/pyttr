#!/usr/bin/env python3
"""Run the local verification suite for pyttr2."""

from __future__ import annotations

import argparse
import ast
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
PYTHON_GLOBS = (
    "*.py",
    "src/pyttr/**/*.py",
    "tests/*.py",
    "scripts/*.py",
)
COPY_IGNORE = (
    ".DS_Store",
    ".git",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".venv",
    "__pycache__",
    "*.egg-info",
    "*.pyc",
    "*.pyo",
    "build",
    "dist",
    "htmlcov",
    "venv",
)


def clean_env(*, include_source: bool = False) -> dict[str, str]:
    env = os.environ.copy()
    env["PIP_DISABLE_PIP_VERSION_CHECK"] = "1"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("PYTHONPATH", None)

    if include_source:
        env["PYTHONPATH"] = os.pathsep.join((str(SRC), str(ROOT)))

    return env


def run(
    args: list[str | Path],
    *,
    cwd: Path = ROOT,
    env: dict[str, str] | None = None,
) -> None:
    command = [str(arg) for arg in args]
    print(flush=True)
    print("==> " + " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, env=env, check=True)


def ast_parse() -> None:
    print(flush=True)
    print("==> AST parse", flush=True)
    paths = [
        path
        for pattern in PYTHON_GLOBS
        for path in ROOT.glob(pattern)
        if path.is_file()
    ]

    for path in paths:
        ast.parse(path.read_text(), filename=str(path))

    print(f"Parsed {len(paths)} Python files", flush=True)


def import_check() -> None:
    code = """
import pyttr.compound_types
import pyttr.core
import pyttr.categorical
import pyttr.probabilistic
import pyttr.model
import pyttr.prelude
import pyttr.prob_compound_types
import pyttr.prob_constraints
import pyttr.prob_predicates
import pyttr.prob_record_types
import pyttr.prob_terms
import pyttr.prob_type_core
import pyttr.probttrtypes
import pyttr.record_types
import pyttr.records
import pyttr.string_types
import pyttr.terms
import pyttr.ttrtypes
import pyttr.type_core
import pyttr.type_ops
import pyttr.utils

from pyttr import probttrtypes, ttrtypes
from pyttr.prob_record_types import RecType as ProbRecType
from pyttr.probttrtypes import BType as PBType, PConstraint
from pyttr.record_types import RecType as ModuleRecType
from pyttr.records import Rec
from pyttr.ttrtypes import BType, RecType

assert pyttr.__all__ == ()
assert ttrtypes.RecType is ModuleRecType
assert pyttr.categorical.RecType is ModuleRecType
assert pyttr.probabilistic.RecType is ProbRecType
assert probttrtypes.RecType is ProbRecType
assert ttrtypes.RecType is not probttrtypes.RecType
for name in ("Type", "BType", "PType", "RecType", "Fun"):
    assert not hasattr(pyttr, name), name
try:
    from pyttr import RecType as RootRecType
except ImportError:
    pass
else:
    raise AssertionError(f"pyttr unexpectedly exported {RootRecType!r}")
assert Rec({"x": "a"}).x == "a"
assert BType("Ind").show() == "Ind"
assert RecType({"x": BType("Ind2")}).show() == "{x : Ind2}"
assert PBType("PInd").show() == "PInd"
assert PConstraint(1).show() == "1.0"
print("imports with warnings-as-errors ok")
"""
    run(
        [sys.executable, "-B", "-W", "error", "-c", code],
        env=clean_env(include_source=True),
    )


def unittest_check() -> None:
    run(
        [sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests"],
        env=clean_env(include_source=True),
    )


def venv_python(venv: Path) -> Path:
    if os.name == "nt":
        return venv / "Scripts" / "python.exe"
    return venv / "bin" / "python"


def copy_project(destination: Path) -> None:
    shutil.copytree(
        ROOT,
        destination,
        ignore=shutil.ignore_patterns(*COPY_IGNORE),
    )


def fresh_install_check() -> None:
    print(flush=True)
    print("==> fresh install smoke test", flush=True)
    with tempfile.TemporaryDirectory(prefix="pyttr2-install-") as tmp:
        tmp_path = Path(tmp)
        project = tmp_path / "project"
        outside = tmp_path / "outside"
        venv = tmp_path / "venv"
        outside.mkdir()
        copy_project(project)

        env = clean_env()
        env["PYTTR2_ORIGINAL_ROOT"] = str(ROOT)

        run(
            [sys.executable, "-m", "venv", "--system-site-packages", venv],
            cwd=tmp_path,
            env=env,
        )

        python = venv_python(venv)
        run(
            [
                python,
                "-m",
                "pip",
                "install",
                "--no-deps",
                project,
            ],
            cwd=outside,
            env=env,
        )

        code = """
import os
from pathlib import Path

import pyttr
import pyttr.core
import pyttr.categorical
import pyttr.probabilistic
import pyttr.prob_constraints
import pyttr.prob_record_types
import pyttr.prob_type_core
from pyttr import probttrtypes, ttrtypes
from pyttr.prob_record_types import RecType as ProbRecType
from pyttr.probttrtypes import BType as PBType, PConstraint
from pyttr.record_types import RecType as ModuleRecType
from pyttr.records import Rec
from pyttr.ttrtypes import BType, RecType

original_root = Path(os.environ["PYTTR2_ORIGINAL_ROOT"]).resolve()
installed_from = Path(pyttr.__file__).resolve()
assert original_root not in installed_from.parents, installed_from
assert pyttr.__all__ == ()
assert ttrtypes.RecType is ModuleRecType
assert pyttr.categorical.RecType is ModuleRecType
assert pyttr.probabilistic.RecType is ProbRecType
assert probttrtypes.RecType is ProbRecType
assert ttrtypes.RecType is not probttrtypes.RecType
for name in ("Type", "BType", "PType", "RecType", "Fun"):
    assert not hasattr(pyttr, name), name
try:
    from pyttr import RecType as RootRecType
except ImportError:
    pass
else:
    raise AssertionError(f"pyttr unexpectedly exported {RootRecType!r}")
assert Rec({"x": "a"}).x == "a"
assert BType("Ind").show() == "Ind"
assert RecType({"x": BType("Ind2")}).show() == "{x : Ind2}"
assert PBType("PInd").show() == "PInd"
assert PConstraint(1).show() == "1.0"
print("fresh install import ok")
"""
        run([python, "-B", "-W", "error", "-c", code], cwd=outside, env=env)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fresh-install-only",
        action="store_true",
        help="only run the fresh-install smoke test",
    )
    parser.add_argument(
        "--skip-fresh-install",
        action="store_true",
        help="skip the fresh-install smoke test",
    )
    args = parser.parse_args()

    if args.fresh_install_only:
        fresh_install_check()
        return

    ast_parse()
    import_check()
    unittest_check()

    if not args.skip_fresh_install:
        fresh_install_check()


if __name__ == "__main__":
    main()
