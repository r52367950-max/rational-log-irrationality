#!/usr/bin/env python3
"""Stage a source-only delivery AFTER root confirms all kernel checks are complete.

This script never runs Lean, never modifies the checked projects, never deletes an
existing delivery, and never creates a ZIP. The caller tests the staged portable
projects before archiving them. Example (only after successful final checks):
  python prepare_delivery.py --checks-complete --audit-log oai017/FINAL_AUDIT.log
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_PARTS = {".lake", ".git", "toolchain", "mathlib4", "verification_dependencies",
                   "library_write_helpers", "node_modules", "__pycache__"}
FORBIDDEN_SUFFIXES = {".olean", ".ilean", ".o", ".a", ".so", ".zst", ".tar", ".zip", ".pyc"}
OLD_MATHLIB = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
NEW_MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
NEW_MODULES = ["DistinctMultiplicativeRigidity", "DistinctMultiplicativePersistent",
               "DistinctMultiplicativeJets", "DistinctMultiplicativeAmple",
               "DistinctMultiplicativeFibre", "DistinctMultiplicativeStatement",
               "RationalLogAnalytic", "OAIApproximationAdapter", "OAIFormalLogAdapter",
               "DistinctMultiplicativeContact", "DistinctMultiplicativeGlobal",
               "DistinctMultiplicativeDegree", "DistinctMultiplicativeExistence",
               "RationalLogParameters", "RationalLogArithmeticAssembly",
               "RationalLogMatrixBridge", "RationalLogGeometryParameters",
               "RationalLogAsymptotic", "RationalLogMain",
               "Round2MainReference", "Round2MainTypeChecker"]
OLD_MODULES = ["ParameterContradiction", "IntegerDeterminant", "Collision", "ApproximationBridge",
               "LaurentResidue", "GeometryNumerics", "RationalCenters"]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def input_path(value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Input must stay inside the review directory: {path}")
    if not path.is_file():
        raise FileNotFoundError(path)
    return path


def validate_log(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    if re.search(r"(?:^|\n)[^\n]*\b(?:error|fatal):", text, re.I):
        raise ValueError(f"Failed-check messages remain in {path}")
    return text


def read_new_audit(path: Path) -> list[dict]:
    text = validate_log(path)
    counts = re.findall(r"\bADAPTER_THEOREM_COUNT\s+(\d+)", text)
    if not counts:
        raise ValueError("The provided log must be the successful final AdapterAxiomAudit log")
    entries: dict[str, dict] = {}
    pattern = r"\bADAPTER_AXIOMS\s+(\S+)\s+#?\[([^\]]*)\]"
    for match in re.finditer(pattern, text, re.S):
        name = match.group(1)
        axioms = [a.strip().strip("`'\"") for a in match.group(2).split(",") if a.strip()]
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise ValueError(f"Unpermitted axiom in {name}: {axioms}")
        item = {"theorem": name, "axioms": axioms}
        if name in entries and entries[name] != item:
            raise ValueError(f"Inconsistent repeated declaration {name}")
        entries[name] = item
    count = int(counts[-1])
    if count <= 0 or len(entries) != count:
        raise ValueError(f"Audit count mismatch: declared {count}, parsed {len(entries)}")
    return [entries[name] for name in sorted(entries)]


def read_old_audit() -> list[dict]:
    entries = json.loads(input_path("portable_project/theorem-axioms.json").read_text())
    if not isinstance(entries, list) or not entries:
        raise ValueError("Missing old-project theorem inventory")
    names = set()
    for entry in entries:
        name = entry["theorem"]
        if name in names or not set(entry["axioms"]) <= ALLOWED_AXIOMS:
            raise ValueError(f"Invalid old-project axiom record: {entry}")
        names.add(name)
    return entries


def verify_upstream() -> tuple[dict, list[Path], list[Path]]:
    provenance = json.loads(input_path("oai017/source-provenance.json").read_text())
    patches = json.loads(input_path("oai017/import-header-patches.json").read_text())
    if patches.get("body_changes") != 0 or provenance.get("errors"):
        raise ValueError("Upstream source or proof-body verification is not clean")
    pristine_base = ROOT / "oai017/source"
    working_base = ROOT / "oai017/working"
    originals, working = [], []
    for item in provenance["files"]:
        rel = Path(item["path"])
        original = input_path(pristine_base / rel)
        candidate = input_path(working_base / rel)
        original_bytes = original.read_bytes()
        candidate_bytes = candidate.read_bytes()
        if digest(original_bytes) != item["sha256"]:
            raise ValueError(f"Pristine source hash changed: {rel}")
        def non_import_bytes(data: bytes) -> bytes:
            return re.sub(rb"(?m)^import [^\r\n]*\r?\n", b"", data)
        if non_import_bytes(candidate_bytes) != non_import_bytes(original_bytes):
            raise ValueError(f"Working source changes mathematical text beyond import lines: {rel}")
        originals.append(original)
        working.append(candidate)
    if len(originals) != provenance["verified_original_blob_count"]:
        raise ValueError("Upstream inventory count mismatch")
    return provenance, originals, working


def lakefile_local() -> str:
    roots = ", ".join("`" + n for n in ["RationalLogReview", *OLD_MODULES, "AxiomAudit"])
    return f'''import Lake
open Lake DSL
package RationalLogReviewDelivery
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "{OLD_MATHLIB}"
@[default_target]
lean_lib RationalLogReview where
  roots := #[{roots}]
'''


def lakefile_oai() -> str:
    roots = ", ".join("`" + n for n in ["OAI017Review", *NEW_MODULES, "AdapterAxiomAudit"])
    return f'''import Lake
open Lake DSL
package OAI017ReviewDelivery where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "{NEW_MATHLIB}"
lean_lib OAI where
  roots := #[`OAI.NumberTheory.PiExponent.Statement]
  globs := #[`OAI.NumberTheory.PiExponent.+]
lean_lib SupportCore
@[default_target]
lean_lib OAI017Review where
  roots := #[{roots}]
'''


def stage(destination: Path, audit_log: Path, extra_logs: list[Path]) -> dict:
    final_receipt = json.loads(input_path("oai017/final-main-receipt.json").read_text())
    required = ["independent_reference_graph_match", "exact_type_match",
                "fresh_builtin_kernel_dependency_replay", "kernel_statement_certificate_checked"]
    if final_receipt.get("status") != "accepted" or not all(final_receipt.get(k) is True for k in required):
        raise ValueError("Full main theorem has not passed the independent final check")
    old_entries = read_old_audit()
    new_entries = read_new_audit(audit_log)
    provenance, originals, working = verify_upstream()
    if destination.exists():
        raise FileExistsError(f"Refusing to replace an existing delivery: {destination}")
    if destination.parent != ROOT:
        raise ValueError("Delivery destination must be a direct child of the review directory")
    temporary = Path(tempfile.mkdtemp(prefix="delivery-staging-", dir=ROOT))
    records: list[dict] = []

    def write(relative: str | Path, data: bytes, source: str = "generated") -> None:
        relative = Path(relative)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe output path: {relative}")
        if FORBIDDEN_PARTS.intersection(relative.parts) or relative.suffix in FORBIDDEN_SUFFIXES:
            raise ValueError(f"Dependency or binary slipped into delivery: {relative}")
        target = temporary / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            raise FileExistsError(f"Duplicate delivery output: {relative}")
        target.write_bytes(data)
        if target.suffix == ".sh":
            target.chmod(0o755)
        records.append({"path":relative.as_posix(), "bytes":len(data), "sha256":digest(data), "source":source})

    def copy(source: str | Path, relative: str | Path) -> None:
        path = input_path(source)
        write(relative, path.read_bytes(), path.relative_to(ROOT).as_posix())

    try:
        template = input_path("DELIVERY_README.zh.md").read_text()
        readme = template.replace("{{LOCAL_THEOREM_COUNT}}", str(len(old_entries)))
        readme = readme.replace("{{OAI_THEOREM_COUNT}}", str(len(new_entries)))
        write("README.md", readme.encode())
        copy("复核与重要性评估.md", "复核与重要性评估.md")
        handled_reports = {"复核与重要性评估.md", "DELIVERY_README.zh.md"}
        for path in sorted(ROOT.glob("*.md")):
            if path.name not in handled_reports:
                copy(path, Path("audits") / path.name)
        for path in sorted((ROOT / "round2").glob("*.md")):
            copy(path, Path("round2") / path.name)
        for folder in ["ns_millennium_source", "ns_comparator_source", "ns_millennium_meta"]:
            for path in sorted((ROOT / "round2" / folder).rglob("*")):
                if path.is_file() and path.suffix in {".lean", ".md", ".json"} or (path.is_file() and path.name in {"LICENSE", "lean-toolchain"}):
                    copy(path, Path("round2") / folder / path.relative_to(ROOT / "round2" / folder))
        copy("oai017/final-main-receipt.json", "checks/final-main-receipt.json")
        for path in sorted((ROOT / "source").glob("*.md")):
            copy(path, Path("manuscript") / path.name)
        for name in ("exact_checks.py", "exact_checks.json", "cech_contraction_check.py", "source_sha256.json"):
            copy(name, Path("checks") / name)
        write("checks/lean-local-theorem-axioms.json", (json.dumps(old_entries,ensure_ascii=False,indent=2)+"\n").encode())
        write("checks/lean-oai017-theorem-axioms.json", (json.dumps(new_entries,ensure_ascii=False,indent=2)+"\n").encode())
        copy(audit_log, "checks/lean-oai017-final-audit.log")
        validate_log(input_path("portable_project/axioms-final.log"))
        copy("portable_project/axioms-final.log", "checks/lean-local-final-audit.log")

        old_dest = Path("lean-local/portable_project")
        for path in sorted((ROOT / "portable_project").glob("*.lean")):
            if path.name != "lakefile.lean":
                copy(path, old_dest / path.name)
        write(old_dest / "lakefile.lean", lakefile_local().encode())
        write(old_dest / "lean-toolchain", b"leanprover/lean4:v4.24.0\n")
        old_manifest = json.loads(input_path("portable_project/lake-manifest.json").read_text())
        old_manifest["name"] = "RationalLogReviewDelivery"
        write(old_dest / "lake-manifest.json", (json.dumps(old_manifest, indent=2) + "\n").encode())
        copy("lean/ENVIRONMENT.md", Path("lean-local") / "ENVIRONMENT.md")

        new_dest = Path("lean-oai017/portable_project")
        for module in NEW_MODULES:
            candidate = ROOT / "oai017" / f"{module}.lean"
            if not candidate.exists():
                candidate = ROOT / "oai017/adapters" / f"{module}.lean"
            copy(candidate, new_dest / candidate.name)
        copy("oai017/AdapterAxiomAudit.lean", new_dest / "AdapterAxiomAudit.lean")
        copy("oai017/SupportCore.lean", new_dest / "SupportCore.lean")
        copy("oai017/verify_round2_main.py", new_dest / "verify_round2_main.py")
        for path in sorted((ROOT / "oai017/verification").iterdir()):
            if path.is_file() and path.suffix in {".lean", ".log", ".json"} and "rational_log_main" in path.name.lower():
                if path.suffix == ".log":
                    validate_log(path)
                copy(path, Path("checks/final-main") / path.name)
        aggregator = "\n".join("import " + n for n in [*NEW_MODULES, "AdapterAxiomAudit"]) + "\n"
        write(new_dest / "OAI017Review.lean", aggregator.encode())
        write(new_dest / "lakefile.lean", lakefile_oai().encode())
        write(new_dest / "lean-toolchain", b"leanprover/lean4:v4.34.1\n")
        new_manifest = json.loads(input_path("oai017/project/lake-manifest.json").read_text())
        new_manifest["name"] = "OAI017ReviewDelivery"
        for item in new_manifest["packages"]:
            if item["name"] == "mathlib":
                item.clear()
                item.update({"type":"git", "url":"https://github.com/leanprover-community/mathlib4.git",
                    "subDir":None, "scope":"", "rev":NEW_MATHLIB, "name":"mathlib",
                    "manifestFile":"lake-manifest.json", "inputRev":NEW_MATHLIB,
                    "inherited":False, "configFile":"lakefile.lean"})
        write(new_dest / "lake-manifest.json", (json.dumps(new_manifest, indent=2) + "\n").encode())
        for path in working:
            copy(path, new_dest / path.relative_to(ROOT / "oai017/working"))
        for path in originals:
            copy(path, Path("oai017-upstream") / path.relative_to(ROOT / "oai017/source"))
        copy("oai017/meta/LICENSE", "oai017-upstream/LICENSE")
        for name in ("source-provenance.json", "import-header-patches.json", "support-imports.json", "target-imports.json", "compiled-upstream-receipt.json", "round2-upstream-receipt.json"):
            copy(Path("oai017") / name, Path("oai017-upstream") / name)

        for path in sorted((ROOT / "oai017").glob("*.md")):
            copy(path, Path("audits/oai017") / path.name)
        for path in sorted((ROOT / "oai017/adapters").iterdir()):
            if path.is_file() and path.suffix in {".md", ".json", ".log"}:
                if path.suffix == ".log":
                    validate_log(path)
                copy(path, Path("checks/oai017-adapters") / path.name)
        for path in sorted((ROOT / "portable_project").glob("*.log")):
            try:
                validate_log(path)
            except ValueError:
                continue
            copy(path, Path("checks/lean-local") / path.name)
        for index, path in enumerate(extra_logs):
            validate_log(path)
            copy(path, Path("checks/additional-successful-logs") / f"{index+1:02d}-{path.name}")
        for name in ("prepare_delivery.py", "DELIVERY_README.zh.md", "verify_delivery.py"):
            copy(name, Path("helpers") / name)
        for folder, target in ((old_dest, "RationalLogReview"), (new_dest, "OAI017Review")):
            check = '#!/usr/bin/env bash\nset -eu\ncd "$(dirname "$0")"\nlake build ' + target + '\n'
            write(folder / "check.sh", check.encode())

        summary = {"main_status":"complete_main_formalization",
                   "main_candidate":final_receipt["candidate"],
                   "remaining_formal_scope":"Sharper explicit C* threshold and smaller LCM constant; neither is needed for main theorem", "local_theorem_count":len(old_entries),
                   "oai017_new_theorem_count":len(new_entries), "pristine_source_count":len(originals),
                   "upstream_commit":provenance["commit"], "file_count":len(records),
                   "total_source_bytes":sum(r["bytes"] for r in records), "files":records}
        if summary["total_source_bytes"] >= 50 * 1024 * 1024:
            raise ValueError("Source-only delivery unexpectedly exceeds 50 MiB")
        write("delivery-manifest.json", (json.dumps(summary,ensure_ascii=False,indent=2)+"\n").encode())
        temporary.rename(destination)
        return {k:v for k,v in summary.items() if k != "files"}
    except BaseException:
        shutil.rmtree(temporary)
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks-complete", action="store_true", help="Root confirms final kernel checks succeeded")
    parser.add_argument("--audit-log", required=True, help="Successful final AdapterAxiomAudit log, relative to review root")
    parser.add_argument("--extra-success-log", action="append", default=[], help="Additional successful build log to preserve")
    parser.add_argument("--output", default="delivery", help="Fresh output folder directly inside the review root")
    args = parser.parse_args()
    if not args.checks_complete:
        parser.error("Do not stage delivery before root confirms completed kernel checks")
    output = Path(args.output)
    if not output.is_absolute():
        output = ROOT / output
    result = stage(output.resolve(), input_path(args.audit_log),
                   [input_path(p) for p in args.extra_success_log])
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__ == "__main__":
    main()
