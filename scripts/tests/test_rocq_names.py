"""Check that the name-table checker rejects wrong lines, renamed Lean names, absent names,
unreadable rows and a wrong count, and reads rows that cite several files.

Inputs: check-rocq-names.py, loaded with runpy, on a small table and source. Output: unittest
results. Requires scripts/check-rocq-names.py.
"""

from pathlib import Path
import runpy
import unittest


CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-rocq-names.py"))
table_failures = CHECKER["table_failures"]

SOURCE = {
    "quadrature2.v": [
        "Definition fbound (g: R -> R) fb := 0.",
        "Lemma g_max_deriv (d : R) : True.",
        "Let g_max_deriv_oneway := 0.",
    ],
    "quadrature.v": ["Lemma intgal_linear1 : True."],
}


def table(line: int, lean: str, unnamed: str, files: str = "`quadrature2.v`",
          count: int = 1) -> str:
    return f"""## Declaration names

| Rocq name | Rocq file | Lean name | Lean module | Same or different, and why |
| --- | --- | --- | --- | --- |
| `fbound` | `quadrature2.v:{line}` | `{lean}` | `Quadrature.Legendre.Bounds` | Same |

### Rocq declarations without a Lean counterpart

The same files contain {count} further declarations.

| Rocq declarations | Rocq file | What the Lean development uses instead |
| --- | --- | --- |
| `{unnamed}` | {files} | Mathlib. |

## Rocq source references
"""


class NameTableTests(unittest.TestCase):
    def check(self, text: str) -> tuple[int, int, list[str]]:
        rows, absent, failures = table_failures(text, SOURCE.__getitem__)
        return len(rows), absent, failures

    def test_matching_table_passes(self):
        self.assertEqual(
            self.check(table(1, "Quadrature.fbound", "g_max_deriv_oneway")), (1, 1, []))

    def test_wrong_line_fails(self):
        self.assertIn("quadrature2.v:2 does not declare fbound",
                      self.check(table(2, "Quadrature.fbound", "g_max_deriv_oneway"))[2])

    def test_renamed_lean_declaration_fails(self):
        self.assertIn("Quadrature.f_bound does not carry the Rocq name fbound",
                      self.check(table(1, "Quadrature.f_bound", "g_max_deriv_oneway"))[2])

    def test_removed_rocq_declaration_fails(self):
        self.assertIn("trigo_cos_e does not occur in `quadrature2.v`",
                      self.check(table(1, "Quadrature.fbound", "trigo_cos_e"))[2])

    def test_row_citing_several_files_passes(self):
        files = "`quadrature2.v`, `quadrature.v`"
        self.assertEqual(
            self.check(table(1, "Quadrature.fbound", "intgal_linear1", files)), (1, 1, []))

    def test_unreadable_row_fails(self):
        files = "`quadrature.v`, `Module Legendre`"
        failures = self.check(table(1, "Quadrature.fbound", "intgal_linear1", files))[2]
        self.assertTrue(any(f.startswith("Unreadable table row") for f in failures))

    def test_wrong_count_fails(self):
        self.assertIn("The document does not state the 1 declarations of the table",
                      self.check(table(1, "Quadrature.fbound", "g_max_deriv_oneway",
                                       count=2))[2])


if __name__ == "__main__":
    unittest.main()
