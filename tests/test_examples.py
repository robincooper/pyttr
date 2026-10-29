import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class ExampleScriptTests(unittest.TestCase):
    def test_record_example_runs(self):
        result = subprocess.run(
            [sys.executable, "-B", "example-records.py"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

        self.assertIn("{f = {f = {ff = a, gg = b}, g = c}", result.stdout)

    def test_type_example_runs(self):
        result = subprocess.run(
            [sys.executable, "-B", "example-types.py"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

        self.assertIn("Example 121", result.stdout)


if __name__ == "__main__":
    unittest.main()
