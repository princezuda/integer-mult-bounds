"""Drift tests for the Lean checks of open PRs #3-#12, and the vendored PR data."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
OPEN = ROOT / "formal" / "open-prs"


class OpenPullRequestLean(unittest.TestCase):
    def test_vendored_data_matches_manifest(self):
        manifest = json.loads((OPEN / "data" / "MANIFEST.json").read_text())
        on_disk = {p.relative_to(OPEN / "data").as_posix()
                   for p in (OPEN / "data").rglob("*") if p.is_file()} - {"MANIFEST.json"}
        self.assertEqual(on_disk, set(manifest["sha256"]))
        for rel, digest in manifest["sha256"].items():
            self.assertEqual(hashlib.sha256((OPEN / "data" / rel).read_bytes()).hexdigest(),
                             digest, rel)

    def test_drift(self):
        for script, args in (("drift_A.py", []), ("drift_B.py", ["--selftest"]),
                             ("drift_C.py", [])):
            result = subprocess.run([sys.executable, "-I", str(OPEN / script), *args],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, script + "\n" + result.stdout + result.stderr)
            self.assertTrue(result.stdout.strip().splitlines()[-1].startswith("OK"), script)


# Each mutation changes a number that the Lean proves or restates, and the named drift test
# must then fail. Mutations 3-10 still compile, so only the drift tests catch them; the
# others also break the Lean build through the ties to the parameters.
# (path under formal/lean, declaration scope or None, [(old, new), ...], drift script):
# with a scope, `old` is replaced throughout that declaration; without, `old` must be unique.
MUTATIONS = [
    ("PRChecksB/PR5.lean", None, [("def aC : ℚ := 7 / 500000000", "def aC : ℚ := 1 / 500000000")],
     "drift_B.py"),
    ("PRChecksB/PR5.lean", None,
     [("(15625 : ℝ) ^ (1 - (aC : ℝ))", "(15625 : ℝ) ^ (1 - (1 / 10 ^ 9 : ℝ))")], "drift_B.py"),
    ("PRChecksC/PR10.lean", None,
     [("def θbar : ℚ := 999 / 1000", "def θbar : ℚ := 9999 / 10000")], "drift_C.py"),
    ("PRChecksB/PR5.lean", None,
     [("κ' < 37 / 25000000000 := by", "κ' < 37 / 2500000000 := by")], "drift_B.py"),
    ("PRChecksB/PR6.lean", "theorem deficit_slack",
     [("aB * (11737 / 1000)", "325 / 10 ^ 11 * (11737 / 1000)")], "drift_B.py"),
    ("PRChecksB/PR5Analytic.lean", None,
     [("def K0LO : ℚ := (333 / 106) / (6932 / 10000)",
       "def K0LO : ℚ := (333 / 107) / (6932 / 10000)")], "drift_B.py"),
    ("PRChecksB/PR5Analytic.lean", None,
     [("π / 4 < 114 / 100 * Real.log 2", "π / 4 < 115 / 100 * Real.log 2")], "drift_B.py"),
    ("PRChecksA/PR3.lean", None,
     [("(1 - (7 / 500000000 : ℝ)) := by", "(1 - (1 / 500000000 : ℝ)) := by\n  -- 7 / 500000000"),
      ("(483 / 50) (7 / 500000000)", "(483 / 50) (1 / 500000000)")], "drift_A.py"),
    ("PRChecksA/PR8.lean", "theorem exponent", [("1 / 250000000", "1 / 10 ^ 9")], "drift_A.py"),
    ("PRChecksC/PR10.lean", "theorem bit_moment :",
     [("246 / 10 ^ 9", "100 / 10 ^ 9"),
      ("theorem bit_moment :\n", "theorem bit_moment :  -- 246 / 10 ^ 9\n")], "drift_C.py"),
    ("PRChecksC/PR9.lean", None, [("(99966136 / 10 ^ 7) ≤", "(99966137 / 10 ^ 7) ≤")], "drift_C.py"),
]


def mutate(text, scope, pairs):
    for old, new in pairs:
        if scope is None:
            assert text.count(old) == 1, old
            text = text.replace(old, new)
        else:
            start = text.index(scope)
            end = text.find("\ntheorem ", start + 1)
            end = len(text) if end < 0 else end
            assert old in text[start:end], (scope, old)
            text = text[:start] + text[start:end].replace(old, new) + text[end:]
    return text


class DriftMutations(unittest.TestCase):
    def test_every_mutation_is_caught(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "formal"
            shutil.copytree(OPEN, dest / "open-prs", ignore=shutil.ignore_patterns("__pycache__"))
            for lib in ("PRChecksA", "PRChecksB", "PRChecksC"):
                shutil.copytree(ROOT / "formal" / "lean" / lib, dest / "lean" / lib)
            shutil.copy(ROOT / "formal" / "lean" / "PRChecksB.lean", dest / "lean")

            def run(script):
                return subprocess.run([sys.executable, "-I", str(dest / "open-prs" / script)],
                                      capture_output=True, text=True)

            for script in ("drift_A.py", "drift_B.py", "drift_C.py"):
                self.assertEqual(run(script).returncode, 0, script)
            for path, scope, pairs, script in MUTATIONS:
                target = dest / "lean" / path
                original = target.read_text()
                target.write_text(mutate(original, scope, pairs))
                try:
                    result = run(script)
                    self.assertNotEqual(result.returncode, 0, f"{script} missed {path}: {pairs}")
                finally:
                    target.write_text(original)


if __name__ == "__main__":
    unittest.main()
