#!/usr/bin/env python3
"""Build the configured CompCert of rocq/certification and check the assembly certificates.

Inputs: --compcert-root, a Git checkout of CompCert 3.17 at COMPCERT_REVISION whose
cparser/Parser.v has been generated (the pinned image has no Menhir); --work-dir, an empty
directory outside the repository; and --jobs for make. Requires Docker and the pinned Coq
image. The script extracts CompCert from Git into the work directory, copies the generated
parser and rocq/certification/Makefile.config, applies configuration.patch, checks the hashes
of configuration-files.json before and after, and rebuilds every CompCert proof. It then
compiles the files of rocq/certification and the files they require against that compiler and
runs Print Assumptions on each of their theorems.

Output: a summary on stdout, and record.json and the logs in the work directory. The check
fails if a file does not compile, if a project file admits a proof or declares an axiom, or if a
theorem depends on an axiom outside rocqcheck.ALLOWED: the configuration defines every compiler
parameter, so none may remain.
"""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True  # keep scripts/ free of __pycache__
import rocqcheck as rc  # noqa: E402

CERTIFICATION = rc.ROCQ / "certification"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    source = args.compcert_root.resolve(strict=True)
    work = rc.empty_work_dir(args.work_dir, source)
    manifest = json.loads((CERTIFICATION / "configuration-files.json").read_text())
    if {rc.git_revision(source), manifest["base_revision"]} != {rc.COMPCERT_REVISION}:
        raise SystemExit(f"CompCert is not at {rc.COMPCERT_REVISION}")
    if rc.sha256(source / "cparser/Parser.v") != manifest["generated_parser_sha256"]:
        raise SystemExit("Unexpected generated parser cparser/Parser.v")
    if rc.sha256(CERTIFICATION / "Makefile.config") != manifest["makefile_config_sha256"]:
        raise SystemExit("Unexpected Makefile.config")

    root = work / "compiler"
    root.mkdir()
    archive = work / "compcert-source.tar"
    with archive.open("wb") as stream:
        subprocess.run(["git", "-C", str(source), "archive", rc.COMPCERT_REVISION],
                       stdout=stream, check=True)
    with tarfile.open(archive) as tar:
        tar.extractall(root, filter="data")
    shutil.copyfile(source / "cparser/Parser.v", root / "cparser/Parser.v")
    shutil.copyfile(CERTIFICATION / "Makefile.config", root / "Makefile.config")

    print("Building the configured CompCert", flush=True)
    (work / "logs").mkdir()
    mounts = {"/compcert": root, "/work": work}
    make = ["/usr/bin/make", f"-j{args.jobs}", f"COQBIN={rc.BIN}"]
    writable = ("/compcert", "/work")
    rc.logged(rc.container(mounts, make + ["depend"], "/compcert", writable),
              work / "logs" / "compcert-depend-original.log")
    for name, hashes in manifest["files"].items():
        if rc.sha256(root / name) != hashes["before"]:
            raise SystemExit(f"Unexpected original CompCert file {name}")
    with (CERTIFICATION / "configuration.patch").open() as patch:
        subprocess.run(["git", "apply", "-"], cwd=root, stdin=patch, check=True)
    for name, hashes in manifest["files"].items():
        if rc.sha256(root / name) != hashes["after"]:
            raise SystemExit(f"Unexpected configured CompCert file {name}")
    rc.logged(rc.container(mounts, make + ["depend"], "/compcert", writable),
              work / "logs" / "compcert-depend.log")
    rc.logged(rc.container(mounts, make + ["proof"], "/compcert", writable),
              work / "logs" / "compcert-proof.log")
    for name, hashes in manifest["files"].items():
        if rc.sha256(root / name) != hashes["after"]:
            raise SystemExit(f"CompCert file {name} changed during the build")

    print("Compiling rocq/certification and its requirements", flush=True)
    targets = [f"certification/{p.name}" for p in sorted(CERTIFICATION.glob("*.v"))]
    names = rc.build_order(targets)
    rc.check_sources(names)
    rc.prepare(work, root, names)
    audited = [t for name in names for t in rc.theorems(name)]
    assumptions = rc.compile_and_audit(work, mounts, rc.load_path([]), names, audited)
    record = {
        "check": "rocq/certification and its requirements, against the configured CompCert 3.17",
        "compcert_revision": rc.COMPCERT_REVISION,
        "configuration_patch_sha256": rc.sha256(CERTIFICATION / "configuration.patch"),
        "configured_files_sha256": {n: rc.sha256(root / n) for n in manifest["files"]},
        "coq_version": subprocess.check_output(
            rc.container({}, [rc.COQC, "--version"], "/"), text=True).strip(),
    }
    rc.finish(work, "check-configured-compcert", record, names, audited, assumptions,
              rc.ALLOWED)


if __name__ == "__main__":
    main()
