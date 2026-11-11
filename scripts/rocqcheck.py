"""Shared code of check-rocq.py and check-configured-compcert.py.

The Rocq files are the .v files under rocq/. A checker copies them into an empty work
directory, compiles them with coqc in the pinned Coq container, without network access, and
audits every theorem with Print Assumptions. It writes its record to the work directory and
prints a summary; nothing is written to the repository.
"""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import textwrap

REPO = Path(__file__).resolve().parents[1]
ROCQ = REPO / "rocq"
COMPCERT_REVISION = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
QUADRULES_SHA256 = "8ffa4ba5b8aae3df243e6d28fd842ec7408259b4d47d21012dd94ce5db21a94d"
IMAGE = "coqorg/coq@sha256:18ebf3da56e60e3ddfd7d4e51f4c53d10241a129f34e93dacbc71562dd43c57a"
BIN = "/home/coq/.opam/4.13.1+flambda/bin/"
COQC = BIN + "coqc"

# Logical axioms of the Rocq standard library and CompCert, and CompCert's axiomatized
# external functions.
ALLOWED = {
    "Axioms.proof_irr",
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Classical_Prop.classic",
    "Eqdep.Eq_rect_eq.eq_rect_eq",
    "external_functions_sem",
    "external_functions_properties",
    "inline_assembly_sem",
    "inline_assembly_properties",
}
# The compiler choices that unmodified CompCert leaves as parameters, to be implemented in
# OCaml; configuration.patch defines them.
COMPILER_PARAMETERS = {
    "Archi.win64", "SelectOp.symbol_is_relocatable", "Inlining.inlining_info",
    "Inlining.inlining_analysis", "Inlining.should_inline", "Allocation.regalloc",
    "RTLgen.more_likely", "Selection.compile_switch", "Selection.if_conversion_heuristic",
    "Linearize.enumerate_aux", "Compiler.print_Cminor", "Compiler.print_RTL",
    "Compiler.print_LTL", "Compiler.print_Mach",
    *(f"Compopts.{name}" for name in [
        "va_strict", "propagate_float_constants", "generate_float_constants",
        "optim_tailcalls", "optim_redundancy", "optim_for_size", "optim_constprop",
        "optim_CSE", "debug"]),
}
# Print Assumptions prints some of these names without their module.
ALIASES = {
    "functional_extensionality_dep": "FunctionalExtensionality.functional_extensionality_dep",
    **{f"Events.{name}": name for name in [
        "external_functions_sem", "external_functions_properties",
        "inline_assembly_sem", "inline_assembly_properties"]},
    **{name.split(".", 1)[1]: name for name in COMPILER_PARAMETERS
       if name.startswith(("Compopts.", "Compiler."))},
}
UNPROVED = re.compile(
    r"\b(?:Admitted|admit|Axioms?|Parameters?|Conjectures?|Abort|native_compute)\b")
REQUIRE = re.compile(r"^From QuadratureC\.(\w+) Require Import ([^.]*)\.", re.M)
THEOREM = re.compile(
    r"^\s*(?:Local\s+)?(?:Theorem|Lemma|Corollary|Fact|Remark|Proposition)\s+([\w']+)")
OPEN = re.compile(r"^\s*(Module|Section)\s+([\w']+)\s*\.")
CLOSE = re.compile(r"^\s*End\s+([\w']+)\s*\.")
COMPCERT_DIRECTORIES = ["lib", "common", "x86_64", "x86", "backend", "cfrontend", "driver",
                        "cparser"]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(text: str) -> str:
    """The text without (* ... *) comments, which nest in Rocq."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def requires(name: str) -> list[str]:
    """The files of rocq/ that rocq/`name` requires."""
    text = (ROCQ / name).read_text()
    return [f"{d}/{n}.v" for d, names in REQUIRE.findall(text) for n in names.split()]


def build_order(targets: list[str]) -> list[str]:
    """`targets` and the files they require, each after its requirements."""
    order: list[str] = []

    def visit(name: str) -> None:
        if name not in order:
            for dependency in requires(name):
                visit(dependency)
            order.append(name)

    for target in targets:
        visit(target)
    return order


def theorems(name: str) -> list[str]:
    """The qualified names of the theorems declared in rocq/`name`."""
    directory, module = name.split("/")[0], Path(name).stem
    stack: list[tuple[str, str]] = []
    found = []
    for line in strip_comments((ROCQ / name).read_text()).splitlines():
        if (match := OPEN.match(line)):
            stack.append((match[1], match[2]))
        elif (match := CLOSE.match(line)) and stack:
            stack.pop()
        elif (match := THEOREM.match(line)):
            modules = [n for kind, n in stack if kind == "Module"]
            found.append(".".join(["QuadratureC", directory, module, *modules, match[1]]))
    return found


def check_sources(names: list[str]) -> None:
    """Reject unproved declarations and native computation in the project files."""
    for name in names:
        text = strip_comments((ROCQ / name).read_text())
        if name != "clight/quadrules.v" and UNPROVED.search(text):
            raise SystemExit(f"rocq/{name}: unproved declaration or native computation")


def prepare(work: Path, compcert: Path, names: list[str]) -> None:
    """Copy the files and CompCert's export/ definitions into `work`."""
    if sha256(ROCQ / "clight/quadrules.v") != QUADRULES_SHA256:
        raise SystemExit("rocq/clight/quadrules.v is not simple_cfem's file at 96d4462")
    for name in names:
        target = work / "proof" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROCQ / name, target)
    (work / "export").mkdir()
    for name in ["Ctypesdefs.v", "Clightdefs.v"]:
        shutil.copyfile(compcert / "export" / name, work / "export" / name)


def container(mounts: dict[str, Path], command: list[str], directory: str = "/work",
              writable: tuple[str, ...] = ("/work",), env: dict[str, str] = {}) -> list[str]:
    """A docker command that runs `command` in the pinned image, without network."""
    arguments = ["docker", "run", "--rm", "--network", "none", "--read-only",
                 "--tmpfs", "/tmp:rw,exec,size=512m", "--user", f"{os.getuid()}:{os.getgid()}",
                 "-e", f"PATH={BIN}:/usr/local/bin:/usr/bin:/bin"]
    for key, value in env.items():
        arguments += ["-e", f"{key}={value}"]
    for target, source in mounts.items():
        mode = "" if target in writable else ":ro"
        arguments += ["-v", f"{source}:{target}{mode}"]
    return arguments + ["-w", directory, "--entrypoint", command[0], IMAGE] + command[1:]


def load_path(extra: list[str]) -> list[str]:
    """coqc flags for CompCert at /compcert and the project at /work/proof."""
    flags = list(extra)
    for name in COMPCERT_DIRECTORIES:
        flags += ["-R", f"/compcert/{name}", f"compcert.{name}"]
    return flags + ["-R", "/compcert/flocq", "Flocq", "-R", "/compcert/MenhirLib", "MenhirLib",
                    "-R", "/work/export", "compcert.export", "-Q", "/work/proof", "QuadratureC"]


def logged(command: list[str], log: Path) -> None:
    print(f"  {log.stem}", flush=True)
    with log.open("w") as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"FAIL {log.stem}:\n{log.read_text()[-8000:]}")


def compile_and_audit(work: Path, mounts: dict[str, Path], flags: list[str],
                      names: list[str], audited: list[str]) -> set[str]:
    """Compile the export files and `names`, then print the assumptions of `audited`."""
    logs = work / "logs"
    logs.mkdir(exist_ok=True)
    for name in ["export/Ctypesdefs.v", "export/Clightdefs.v"] + [f"proof/{n}" for n in names]:
        logged(container(mounts, [COQC, *flags, f"/work/{name}"]),
               logs / (name.removesuffix(".v").replace("/", ".") + ".log"))
    theorems_ = [name for name in names if name != "clight/quadrules.v"]
    audit = work / "proof" / "Audit.v"
    audit.write_text("".join(
        f"From QuadratureC.{n.split('/')[0]} Require {Path(n).stem}.\n" for n in theorems_) +
        "".join(f"Print Assumptions {name}.\n" for name in audited))
    log = logs / "Audit.log"
    logged(container(mounts, [COQC, *flags, "/work/proof/Audit.v"]), log)
    text = log.read_text()
    count = text.count("Axioms:\n") + text.count("Closed under the global context")
    if count != len(audited):
        raise SystemExit(f"Expected {len(audited)} assumption audits, found {count}")
    found = set()
    for section in text.split("Axioms:\n")[1:]:
        found.update(re.findall(r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M))
    return {ALIASES.get(name, name) for name in found}


def finish(work: Path, title: str, record: dict, names: list[str], audited: list[str],
           assumptions: set[str], allowed: set[str]) -> None:
    """Fail on an unexpected assumption; otherwise write the record and print the summary."""
    unexpected = assumptions - allowed
    record.update({
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "container_image": IMAGE,
        "files": {f"rocq/{n}": sha256(ROCQ / n) for n in names},
        "audited_theorems": audited,
        "assumptions": sorted(assumptions),
        "unexpected_assumptions": sorted(unexpected),
    })
    (work / "record.json").write_text(json.dumps(record, indent=2) + "\n")
    parameters = assumptions & COMPILER_PARAMETERS
    axioms = "\n    ".join(textwrap.wrap(", ".join(sorted(assumptions - parameters)), 92))
    print(f"\n{title}: {'FAIL' if unexpected else 'PASS'}")
    print(f"  Rocq files compiled: {len(names)}")
    print(f"  theorems audited:    {len(audited)}")
    print(f"  axioms used:\n    {axioms or 'none'}")
    if parameters:
        print(f"  compiler parameters: {len(parameters)} of CompCert's backend choices, listed in "
              "record.json")
    if unexpected:
        print(f"  not allowed:         {', '.join(sorted(unexpected))}")
    print(f"  record:              {work / 'record.json'}")
    if unexpected:
        raise SystemExit(1)


def empty_work_dir(path: Path, *sources: Path) -> Path:
    """`path`, which must be empty or absent and outside the repository and the sources."""
    work = path.resolve()
    for source in (REPO, *sources):
        if work.is_relative_to(source.resolve()):
            raise SystemExit(f"The work directory must be outside {source}")
    if work.exists() and any(work.iterdir()):
        raise SystemExit("The work directory must be empty")
    work.mkdir(parents=True, exist_ok=True)
    return work


def git_revision(root: Path) -> str:
    return subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"],
                                   text=True).strip()
