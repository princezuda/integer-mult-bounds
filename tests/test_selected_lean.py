"""`Selected.lean` is regenerated from the certificate JSON without changes."""
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]


class SelectedLean(unittest.TestCase):
    def test_generated_file_is_current(self):
        result = subprocess.run([sys.executable, str(ROOT/'formal'/'lean'/'gen_selected.py'), '--check'],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)


if __name__ == '__main__':
    unittest.main()
