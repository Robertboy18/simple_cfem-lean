"""Tests of check-lean.py: a source module that the audit does not see fails the check.

Run with `python3 -m pytest -p no:rerunfailures scripts/tests`.
"""

from pathlib import Path
import runpy
import tempfile
import unittest

unaudited_modules = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check-lean.py"))["unaudited_modules"]


def tree(*names: str) -> tempfile.TemporaryDirectory:
    directory = tempfile.TemporaryDirectory()
    for name in names:
        path = Path(directory.name) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("")
    return directory


class UnauditedModules(unittest.TestCase):
    def test_complete(self):
        with tree("Quadrature/Gaussian/Rule.lean") as root:
            log = 'Project modules: ["Quadrature","Quadrature.Gaussian.Rule"]\n'
            self.assertEqual(unaudited_modules(log, Path(root)), [])

    def test_unimported_file(self):
        with tree("Quadrature/Gaussian/Rule.lean", "Quadrature/Unused.lean") as root:
            log = 'Project modules: ["Quadrature","Quadrature.Gaussian.Rule"]\n'
            self.assertEqual(unaudited_modules(log, Path(root)), ["Quadrature.Unused"])

    def test_module_without_file(self):
        with tree() as root:
            log = 'Project modules: ["Quadrature","Quadrature.Removed"]\n'
            self.assertEqual(unaudited_modules(log, Path(root)), ["Quadrature.Removed"])

    def test_missing_inventory(self):
        with tree() as root, self.assertRaises(SystemExit):
            unaudited_modules("Audited 1 Quadrature theorems\n", Path(root))


if __name__ == "__main__":
    unittest.main()
