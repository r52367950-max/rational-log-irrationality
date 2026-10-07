#!/usr/bin/env python3
"""Check a named final theorem against an independent stock-object proposition.

This is exact-type plus normal Lean kernel checking, not sandboxed/exported
Comparator or nanoda. It replays the target dependency closure in a fresh Lean kernel
environment. A theorem still requiring geometry hypotheses is rejected.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = Path(__file__).resolve().parent
OUT = BASE / "verification"
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_check(source: Path, log: Path, runner: str, project_dir: Path) -> int:
    if runner == "workspace":
        cmd = [str(BASE / "check.sh"), "--adapter", str(source)]
    else:
        build_lib = project_dir / ".lake/build/lib/lean"
        build_lib.mkdir(parents=True, exist_ok=True)
        cmd = ["lake", "env", "lean", "-DautoImplicit=false",
               "--root=" + str(source.parent), str(source),
               "-o", str(build_lib / (source.stem + ".olean")),
               "-i", str(build_lib / (source.stem + ".ilean"))]
    with log.open("w") as stream:
        result = subprocess.run(
            cmd, cwd=project_dir,
            stdout=stream, stderr=subprocess.STDOUT, check=False,
        )
    return result.returncode


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--module", action="append", required=True,
                    help="Already emitted module containing the candidate; repeat for imports")
    ap.add_argument("--theorem", required=True, help="Fully qualified theorem name")
    ap.add_argument("--source", action="append", default=[],
                    help="Recompile solution sources in dependency order before checking")
    ap.add_argument("--expect-reject", action="store_true",
                    help="Exercise rejection of a known conditional theorem")
    ap.add_argument("--runner", choices=["auto", "workspace", "lake"], default="auto",
                    help="Portable lake runner, or this session's compatibility wrapper")
    ap.add_argument("--project-dir", type=Path,
                    help="Lake project root; defaults to project/ if present, else script directory")
    ap.add_argument("--output-dir", type=Path, default=OUT,
                    help="Receipt/log directory; defaults to verification/ beside the script")
    ap.add_argument("--prepare-checker", action="store_true",
                    help="Compile reference and checker on a fresh portable checkout")
    args = ap.parse_args()
    if any(not IDENT.fullmatch(x) for x in args.module + [args.theorem]):
        ap.error("Module and declaration names must be plain qualified Lean identifiers")
    runner = args.runner
    if runner == "auto":
        runner = "workspace" if (BASE / "check.sh").is_file() else "lake"
    project_dir = (args.project_dir or (BASE / "project" if
                   (BASE / "project/lakefile.lean").is_file() else BASE)).resolve()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    label = args.theorem.replace(".", "_")
    receipt = {
        "candidate": args.theorem,
        "modules": args.module,
        "reference": "RationalLogReview.MainReference.StrictRationalLogMain",
        "reference_sha256": sha(BASE / "Round2MainReference.lean"),
        "checker_sha256": sha(BASE / "Round2MainTypeChecker.lean"),
        "lean": "4.34.1",
        "mathlib_commit": "d13f23b723b8a846827a245b89c10fc7d3f11612",
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "nanoda_run": False,
        "comparator_run": False,
        "exported_environment_replay": False,
        "fresh_builtin_kernel_dependency_replay": False,
        "source_checks": [],
        "runner": runner,
        "project_dir": str(project_dir),
        "validator_sha256": sha(Path(__file__).resolve()),
    }
    if args.prepare_checker:
        for name in ["Round2MainReference.lean", "Round2MainTypeChecker.lean"]:
            log = output_dir / (label + ".prepare." + name + ".log")
            code = run_check(BASE / name, log, runner, project_dir)
            if code:
                print(f"CHECKER_PREPARATION_REJECTED {name}; see {log}")
                return code
    for index, rel in enumerate(args.source):
        p = Path(rel)
        if not p.is_absolute():
            p = BASE / p
        p = p.resolve()
        log = output_dir / f"{label}.source{index}.log"
        code = run_check(p, log, runner, project_dir)
        receipt["source_checks"].append({"source": str(p), "sha256": sha(p),
                                         "log": str(log), "exit_code": code})
        if code:
            receipt["status"] = "source_rejected"
            (output_dir / f"{label}.receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            print(f"SOURCE_REJECTED {p}; see {log}")
            return code

    imports = "\n".join("import " + module for module in args.module)
    header = (
        "import Round2MainReference\nimport Round2MainTypeChecker\n" + imports + "\n\n"
        "set_option autoImplicit false\n\n"
    )
    source = output_dir / f"{label}_Guard.lean"
    source.write_text(
        header +
        f"#verify_and_replay_rational_log_main {args.theorem}\n\n"
    )
    log = output_dir / f"{label}.check.log"
    code = run_check(source, log, runner, project_dir)
    log_text = log.read_text()
    receipt.update({"guard_source": str(source), "guard_sha256": sha(source),
                    "log": str(log), "log_sha256": sha(log), "guard_exit_code": code,
                    "independent_reference_graph_match":
                        "INDEPENDENT_REFERENCE_GRAPH_MATCH" in log_text,
                    "exact_type_match": "FINAL_TYPE_MATCH" in log_text,
                    "fresh_builtin_kernel_dependency_replay":
                        "FRESH_KERNEL_REPLAY_ACCEPTED" in log_text,
                    "kernel_statement_certificate_checked": False,
                    "status": "guard_accepted" if code == 0 else "rejected"})
    receipt_path = output_dir / f"{label}.receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    if args.expect_reject:
        if code == 0:
            print("REJECTION_SELF_TEST_FAILED: conditional target unexpectedly matched")
            return 1
        if "FINAL_TYPE_MISMATCH" not in log_text:
            print(f"REJECTION_SELF_TEST_INCONCLUSIVE: failure was not a type mismatch; see {log}")
            return 1
        print(f"EXPECTED_FINAL_TYPE_MISMATCH {args.theorem}; see {log}")
        return 0
    if code:
        print(f"FINAL_REJECTED {args.theorem}; see {log}")
        return code

    # Create a proof certificate only after the complete target type has matched
    # and the original proof closure has replayed successfully. A rejected
    # conditional theorem therefore never produces an error-recovery proof.
    certificate = output_dir / f"{label}_Certificate.lean"
    certificate.write_text(
        header +
        "namespace RationalLogReview.IndependentFinalCheck\n"
        "theorem statement_certificate :\n"
        "    RationalLogReview.MainReference.StrictRationalLogMain :=\n"
        f"  {args.theorem}\n"
        "end RationalLogReview.IndependentFinalCheck\n\n"
        "#print axioms RationalLogReview.IndependentFinalCheck.statement_certificate\n"
    )
    certificate_log = output_dir / f"{label}.certificate.log"
    code = run_check(certificate, certificate_log, runner, project_dir)
    receipt.update({"certificate_source": str(certificate),
                    "certificate_sha256": sha(certificate),
                    "certificate_log": str(certificate_log),
                    "certificate_log_sha256": sha(certificate_log),
                    "exit_code": code,
                    "kernel_statement_certificate_checked": code == 0,
                    "status": "accepted" if code == 0 else "rejected"})
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    if code:
        print(f"FINAL_REJECTED {args.theorem}; see {log}")
        return code
    print(f"FINAL_ACCEPTED_EXACT_TYPE_AND_AXIOMS {args.theorem}; see {log}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
