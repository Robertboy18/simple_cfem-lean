"""Tests of the Rocq file handling in rocqcheck.py, on rocq/ itself.

Every .v file is in _CoqProject, every QuadratureC requirement names a file, the build order puts
each file after its requirements, and the two checkers together compile every file.
"""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import rocqcheck as rc  # noqa: E402

FILES = sorted(str(p.relative_to(rc.ROCQ)) for p in rc.ROCQ.rglob("*.v"))


class RocqFiles(unittest.TestCase):
    def test_coq_project_lists_every_file(self):
        listed = [line for line in (rc.ROCQ / "_CoqProject").read_text().splitlines()
                  if line.endswith(".v")]
        self.assertEqual(sorted(listed), FILES)
        self.assertEqual(listed, rc.build_order(listed))

    def test_requirements_exist(self):
        for name in FILES:
            for dependency in rc.requires(name):
                self.assertIn(dependency, FILES, f"{name} requires {dependency}")

    def test_build_order(self):
        order = rc.build_order(FILES)
        self.assertEqual(sorted(order), FILES)
        for name in order:
            for dependency in rc.requires(name):
                self.assertLess(order.index(dependency), order.index(name))

    def test_checkers_cover_every_file(self):
        release = rc.build_order([f for f in FILES if not f.startswith("certification/")])
        configured = rc.build_order([f for f in FILES if f.startswith("certification/")])
        self.assertFalse([f for f in release if f.startswith("certification/")])
        self.assertEqual(set(release) | set(configured), set(FILES))

    def test_no_unproved_declarations(self):
        rc.check_sources(FILES)

    def test_theorem_names(self):
        names = rc.theorems("clight/SilentTermination.v")
        self.assertIn(
            "QuadratureC.clight.SilentTermination.SilentTermination.termination_prefix", names)
        self.assertIn("QuadratureC.clight.ClightRules.integrate_rule_steps",
                      rc.theorems("clight/ClightRules.v"))

    def test_strip_comments(self):
        self.assertEqual(rc.strip_comments("a (* b (* c *) d *) e"), "a  e")


if __name__ == "__main__":
    unittest.main()
