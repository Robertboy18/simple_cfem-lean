#!/usr/bin/env python3
"""Check the declaration-name tables of docs/comparison.md against simple_cfem and Lean.

Inputs: --simple-cfem, a Git checkout of VeriNum/simple_cfem at REVISION, and the built Lean
library. Output: a summary on stdout.
Every row of the name table must cite a line of a simple_cfem file that declares its Rocq name,
and a Lean declaration with the same last component in the cited module. A Lean run over
`import Quadrature` checks the defining modules. Every name in the table of Rocq declarations
without a Lean counterpart must occur in one of the files that row cites, and the document must
state how many there are. A row of either table that does not have the expected form fails the
check.
"""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Callable

REVISION = "96d4462f8cb1a31ac31990a173da4edcfe7f6852"
DOC = Path("docs/comparison.md")
NAMED = re.compile(r"\| `([^`]+)` \| `([^`:]+):(\d+)` \| `([^`]+)` \| `([^`]+)` \|")
UNNAMED = re.compile(r"\| ((?:`[^`]+`(?:, )?)+) \| ((?:`[^`]+\.v`(?:, )?)+) \|")
COUNT = re.compile(r"The same files contain (\d+) further declarations")
DECLARATION = re.compile(
    r"^\s*(?:Local |Program )?(?:Lemma|Theorem|Definition|Let|Record|Fixpoint|Corollary|Fact)\b"
    r"|^\s*[\w']+\s*:")


def word(name: str) -> re.Pattern[str]:
    return re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")


def section(text: str, heading: str) -> str:
    start = text.index(heading)
    end = text.find("\n## ", start + len(heading))
    return text[start:end if end >= 0 else len(text)]


def table(text: str, header: str, row: re.Pattern[str], failures: list[str]
          ) -> list[tuple[str, ...]]:
    """The rows of the table whose header line starts with `header`, matched against `row`.

    Every body line up to the end of the table must match; the others are failures."""
    lines = text[text.index("\n" + header) + 1:].split("\n")
    rows = []
    for line in lines[2:]:
        if not line.startswith("|"):
            break
        match = row.match(line)
        if match is None:
            failures.append(f"Unreadable table row: {line[:100]}")
        else:
            rows.append(match.groups())
    return rows


def table_failures(text: str, source: Callable[[str], list[str]]
                   ) -> tuple[list[tuple[str, ...]], int, list[str]]:
    """Check both tables against `source`, which gives the lines of a simple_cfem proof file.

    Returns the rows of the name table, the number of names without a Lean counterpart, and the
    failures found."""
    names = section(text, "## Declaration names")
    failures: list[str] = []
    rows = table(names, "| Rocq name |", NAMED, failures)
    unnamed = table(names, "| Rocq declarations |", UNNAMED, failures)
    for rocq, file, line, lean, _ in rows:
        lines = source(file)
        cited = lines[int(line) - 1] if 0 < int(line) <= len(lines) else ""
        if not (word(rocq).search(cited) and DECLARATION.search(cited)):
            failures.append(f"{file}:{line} does not declare {rocq}")
        if lean.split(".")[-1] != rocq:
            failures.append(f"{lean} does not carry the Rocq name {rocq}")
    absent = 0
    for listed, files in unnamed:
        texts = ["\n".join(source(f)) for f in re.findall(r"`([^`]+)`", files)]
        for rocq in re.findall(r"`([^`]+)`", listed):
            absent += 1
            if not any(word(rocq).search(t) for t in texts):
                failures.append(f"{rocq} does not occur in {files}")
    stated = COUNT.search(names)
    if stated is None or int(stated[1]) != absent:
        failures.append(f"The document does not state the {absent} declarations of the table")
    return rows, absent, failures


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--simple-cfem", type=Path, required=True)
    args = parser.parse_args()
    checkout = args.simple_cfem.resolve()
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if revision != REVISION:
        raise SystemExit(f"simple_cfem is at {revision}, not {REVISION}")
    sources: dict[str, list[str]] = {}

    def source(name: str) -> list[str]:
        if name not in sources:
            sources[name] = (checkout / "proof" / name).read_text().split("\n")
        return sources[name]

    rows, absent, failures = table_failures((root / DOC).read_text(), source)
    pairs = ", ".join(f'("{lean}", "{module}")' for _, _, _, lean, module in rows)
    check = f"""import Quadrature

open Lean in
run_cmd do
  let env ← getEnv
  for (decl, module) in #[{pairs}] do
    match env.getModuleIdxFor? decl.toName with
    | some i =>
      unless env.header.moduleNames[i.toNat]! == module.toName do
        throwError m!"{{decl}} is not declared in {{module}}"
    | none => throwError m!"{{decl}} is not declared"
  logInfo m!"Checked Lean names in their modules"
"""
    with tempfile.TemporaryDirectory(prefix="simple-cfem-lean-names-") as directory:
        lean_file = Path(directory) / "RocqNames.lean"
        lean_file.write_text(check)
        result = subprocess.run(["lake", "env", "lean", str(lean_file)], cwd=root,
                                capture_output=True, text=True)
    log = result.stdout + result.stderr
    if result.returncode or "Checked Lean names in their modules" not in log:
        failures.append("Lean check failed:\n" + log[-4000:])
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"check-rocq-names: PASS\n  named rows:          {len(rows)}\n"
          f"  without counterpart: {absent}\n  simple_cfem:         {REVISION[:7]}")


if __name__ == "__main__":
    main()
