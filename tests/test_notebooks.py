import os
import tempfile
import unittest
from pathlib import Path

import nbformat
from nbclient import NotebookClient


ROOT = Path(__file__).resolve().parents[1]
NOTEBOOKS = sorted(ROOT.glob("*.ipynb"))


class NotebookTests(unittest.TestCase):
    def test_notebooks_execute(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            previous_ipython_dir = os.environ.get("IPYTHONDIR")
            os.environ["IPYTHONDIR"] = tmpdir
            try:
                for path in NOTEBOOKS:
                    with self.subTest(notebook=path.name):
                        nb = nbformat.read(path, as_version=4)
                        client = NotebookClient(
                            nb,
                            timeout=120,
                            kernel_name="python3",
                            resources={"metadata": {"path": str(ROOT)}},
                        )
                        client.execute()
            finally:
                if previous_ipython_dir is None:
                    os.environ.pop("IPYTHONDIR", None)
                else:
                    os.environ["IPYTHONDIR"] = previous_ipython_dir


if __name__ == "__main__":
    unittest.main()
