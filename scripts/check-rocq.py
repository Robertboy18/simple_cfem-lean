#!/usr/bin/env python3
"""Compile the Rocq proofs against CompCert 3.17 and audit the assumptions of every theorem.

Inputs: --compcert-root, a built x86_64 CompCert 3.17 tree at COMPCERT_REVISION, unmodified;
--mathcomp-root and --coquelicot-root, Git checkouts at the revisions in DEPENDENCIES; and
--work-dir, an empty directory outside the repository. Requires Docker and the pinned Coq
image. The script exports MathComp and Coquelicot from Git, builds the part of MathComp that
Coquelicot needs and Coquelicot itself, then compiles every file of rocq/ except certification/
in dependency order and runs Print Assumptions on each of their theorems. CompCert's own
proofs are used as built in --compcert-root, which is mounted read-only.

Output: a summary on stdout, and record.json and the logs in the work directory. The check
fails if a file does not compile, if a project file admits a proof or declares an axiom, or if a
theorem depends on an axiom outside rocqcheck.ALLOWED and the compiler parameters of CompCert.
"""

import argparse
import subprocess
from pathlib import Path
import sys

sys.dont_write_bytecode = True  # keep scripts/ free of __pycache__
import rocqcheck as rc  # noqa: E402

DEPENDENCIES = {
    "mathcomp": ("1.19.0", "f7528eb05b49bca45fb07e274021a8c4a3200efb"),
    "coquelicot": ("3.4.2", "594b782cef83a8ae214c44152c72dcb80f88d93c"),
}


def export(root: Path, revision: str, destination: Path) -> None:
    """Extract `revision` of the clean Git checkout `root` into `destination`."""
    if rc.git_revision(root) != revision:
        raise SystemExit(f"{root} is not at {revision}")
    subprocess.run(["git", "-C", str(root), "diff", "--quiet", "HEAD"], check=True)
    destination.mkdir(parents=True)
    archive = subprocess.Popen(["git", "-C", str(root), "archive", revision],
                               stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", str(destination)], stdin=archive.stdout, check=True)
    if archive.wait():
        raise SystemExit(f"git archive failed in {root}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--mathcomp-root", type=Path, required=True)
    parser.add_argument("--coquelicot-root", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    compcert = args.compcert_root.resolve(strict=True)
    roots = {"mathcomp": args.mathcomp_root.resolve(strict=True),
             "coquelicot": args.coquelicot_root.resolve(strict=True)}
    work = rc.empty_work_dir(args.work_dir, compcert, *roots.values())
    if rc.git_revision(compcert) != rc.COMPCERT_REVISION:
        raise SystemExit(f"CompCert is not at {rc.COMPCERT_REVISION}")
    subprocess.run(["git", "-C", str(compcert), "diff", "--quiet", "HEAD", "--", "*.v"],
                   check=True)
    if not (compcert / "driver/Compiler.vo").is_file():
        raise SystemExit("CompCert is not built")

    targets = [str(p.relative_to(rc.ROCQ)) for p in sorted(rc.ROCQ.rglob("*.v"))
               if p.parent.name != "certification"]
    names = rc.build_order(targets)
    rc.check_sources(names)
    rc.prepare(work, compcert, names)

    print("Building MathComp and Coquelicot", flush=True)
    for name, root in roots.items():
        export(root, DEPENDENCIES[name][1], work / "dependencies" / name)
    mounts = {"/compcert": compcert, "/work": work}
    env = {"COQBIN": rc.BIN, "COQPATH": "/work/dependencies/mathcomp"}
    (work / "logs").mkdir()
    for label, command, directory in [
        ("mathcomp", ["make", "-j8", "seq.vo"], "mathcomp/mathcomp/ssreflect"),
        ("coquelicot-autoconf", ["autoconf"], "coquelicot"),
        ("coquelicot-configure", ["./configure"], "coquelicot"),
        ("coquelicot", ["./remake", "-j8"], "coquelicot"),
    ]:
        rc.logged(rc.container(mounts, command, f"/work/dependencies/{directory}", env=env),
                  work / "logs" / f"{label}.log")

    print("Compiling rocq/", flush=True)
    flags = rc.load_path([
        "-R", "/work/dependencies/mathcomp/mathcomp/ssreflect", "mathcomp.ssreflect",
        "-R", "/work/dependencies/coquelicot/theories", "Coquelicot"])
    audited = [t for name in names for t in rc.theorems(name)]
    assumptions = rc.compile_and_audit(work, mounts, flags, names, audited)
    record = {
        "check": "rocq/ except certification/, against CompCert 3.17",
        "compcert_revision": rc.COMPCERT_REVISION,
        "dependencies": {name: {"version": v, "revision": r}
                         for name, (v, r) in DEPENDENCIES.items()},
        "coq_version": subprocess.check_output(
            rc.container({}, [rc.COQC, "--version"], "/"), text=True).strip(),
        "compiler_parameters": sorted(assumptions & rc.COMPILER_PARAMETERS),
    }
    rc.finish(work, "check-rocq", record, names, audited, assumptions,
              rc.ALLOWED | rc.COMPILER_PARAMETERS)


if __name__ == "__main__":
    main()
