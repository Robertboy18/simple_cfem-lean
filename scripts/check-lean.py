#!/usr/bin/env python3
"""Build the Lean libraries and audit the axioms of their theorems.

Runs `lake build` and then `lake env lean scripts/Audit.lean`, which fails if a theorem of
Quadrature or CCLib depends on an axiom other than propext, Classical.choice and Quot.sound, or if
either library declares an axiom. The script also fails if a Lean file under Quadrature/ is not
imported, directly or not, by Quadrature.lean, since the audit would not see it, and if a
dependency in .lake/packages is not at the revision of lake-manifest.json or has local changes.
Requires elan. Prints a summary; the only files it writes are the build outputs of `lake build`
under .lake.
"""

import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(command: list[str]) -> str:
    """The output of `command`, run in the repository; exit with its log if it fails."""
    print("$ " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"{result.stdout[-10000:]}\nFAIL: {' '.join(command)}")
    return result.stdout


def unaudited_modules(audit_log: str, root: Path = ROOT) -> list[str]:
    """The modules of Quadrature/ that the audit did not see, and modules without a file."""
    match = re.search(r"^Project modules: (\[.*\])$", audit_log, flags=re.MULTILINE)
    if match is None:
        raise SystemExit("The audit did not print its modules")
    seen = set(json.loads(match[1]))
    files = {"Quadrature"} | {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "Quadrature").rglob("*.lean")
    }
    return sorted(files ^ seen)


def check_dependencies() -> int:
    """Check every Git dependency of lake-manifest.json; return how many there are."""
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    for package in packages:
        name = package["name"].removeprefix("«").removesuffix("»")
        checkout = ROOT / ".lake/packages" / name
        revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                           text=True).strip()
        status = subprocess.check_output(["git", "-C", str(checkout), "status", "--porcelain"],
                                         text=True)
        if revision != package["rev"] or status:
            raise SystemExit(f"FAIL: {name} is not at {package['rev']} or has local changes")
    return len(packages)


def main() -> None:
    build = run(["lake", "build"])
    warnings = build.count("warning:")
    audit = run(["lake", "env", "lean", "-DwarningAsError=true", "scripts/Audit.lean"])
    missing = unaudited_modules(audit)
    if missing:
        raise SystemExit("FAIL: not imported by Quadrature.lean, or without a source file: "
                         + ", ".join(missing))
    dependencies = check_dependencies()
    counts = re.search(r"Audited (\d+) Quadrature theorems and (\d+) CCLib theorems", audit)
    jobs = re.search(r"Build completed successfully \((\d+) jobs\)", build)
    print("\ncheck-lean: PASS")
    print(f"  lake build:          {jobs[1] if jobs else '?'} jobs, {warnings} warnings")
    print(f"  Quadrature theorems: {counts[1]}")
    print(f"  CCLib theorems:      {counts[2]}")
    print("  axioms allowed:      propext, Classical.choice, Quot.sound")
    print(f"  dependencies:        {dependencies}, at the revisions of lake-manifest.json")


if __name__ == "__main__":
    main()
