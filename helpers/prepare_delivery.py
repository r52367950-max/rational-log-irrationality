#!/usr/bin/env python3
"""Refresh the repository's source manifest or export a checked source bundle.

Run from any directory:
  python helpers/prepare_delivery.py --refresh-manifest
  python helpers/prepare_delivery.py --output /tmp/rational-log-delivery

This script does not run Lean or issue a new mathematical verification receipt.
It preserves the existing proof-source hashes and checks the recorded receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_PARTS = {".git", ".lake", "__pycache__", "node_modules",
                  "toolchain", "mathlib4", "verification_dependencies",
                  "library_write_helpers"}
EXCLUDED_SUFFIXES = {".olean", ".ilean", ".o", ".a", ".so", ".dll",
                     ".pyc", ".zst", ".tar", ".zip", ".bundle"}
REMOVED_NS = {"ns_millennium_source", "ns_comparator_source", "ns_millennium_meta"}
PROOF_ROOTS = {"lean-local", "lean-oai017", "oai017-upstream"}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_files(root: Path) -> list[Path]:
    """Use Git's source inventory when present; support extracted bundles too."""
    if (root / ".git").exists():
        output = subprocess.check_output(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
            cwd=root,
        )
        candidates = [root / name for name in output.decode("utf-8").split("\0") if name]
    else:
        candidates = list(root.rglob("*"))
    sources = []
    for path in candidates:
        rel = path.relative_to(root)
        if (rel.as_posix() == "delivery-manifest.json"
                or EXCLUDED_PARTS.intersection(rel.parts)
                or path.suffix in EXCLUDED_SUFFIXES
                or (rel.parts[0] == "round2" and REMOVED_NS.intersection(rel.parts))):
            continue
        if path.is_symlink():
            raise ValueError(f"Source bundle must not contain a symlink: {rel}")
        if not path.is_file():
            continue
        if not path.resolve().is_relative_to(root):
            raise ValueError(f"Source path escapes repository: {rel}")
        sources.append(path)
    return sorted(set(sources))


def guard_existing_proofs(root: Path, manifest: dict, sources: list[Path]) -> None:
    """Documentation repackaging must not silently certify modified Lean code."""
    old = {item["path"]: item for item in manifest["files"]}
    actual = {path.relative_to(root).as_posix(): path for path in sources}
    protected = {name for name in old
                 if name.endswith(".lean") and Path(name).parts[0] in PROOF_ROOTS}
    for name in protected:
        if name not in actual or sha256(actual[name].read_bytes()) != old[name]["sha256"]:
            raise ValueError(f"Lean proof source changed; obtain fresh verification first: {name}")
    for name in actual:
        if name.endswith(".lean") and Path(name).parts[0] in PROOF_ROOTS and name not in old:
            raise ValueError(f"Unverified Lean source is not covered by the existing manifest: {name}")
    receipt_path = root / "checks/final-main-receipt.json"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    if sha256(receipt_path.read_bytes()) != old["checks/final-main-receipt.json"]["sha256"]:
        raise ValueError("The existing main-theorem verification receipt changed")
    required = ["independent_reference_graph_match", "exact_type_match",
                "fresh_builtin_kernel_dependency_replay", "kernel_statement_certificate_checked"]
    if (receipt.get("status") != "accepted"
            or receipt.get("candidate") != manifest["main_candidate"]
            or not all(receipt.get(key) is True for key in required)):
        raise ValueError("The existing main-theorem receipt does not record acceptance")


def refresh_manifest(root: Path) -> dict:
    path = root / "delivery-manifest.json"
    manifest = json.loads(path.read_text(encoding="utf-8"))
    sources = source_files(root)
    guard_existing_proofs(root, manifest, sources)
    old = {item["path"]: item for item in manifest["files"]}
    records = []
    for source in sources:
        name = source.relative_to(root).as_posix()
        data = source.read_bytes()
        records.append({"path": name, "bytes": len(data), "sha256": sha256(data),
                        "source": old.get(name, {}).get("source", "repository")})
    total = sum(item["bytes"] for item in records)
    if total >= 50 * 1024 * 1024:
        raise ValueError("Source-only delivery unexpectedly exceeds 50 MiB")
    manifest.update(files=records, file_count=len(records), total_source_bytes=total)
    path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return manifest


def export_bundle(root: Path, destination: Path, manifest: dict) -> None:
    if destination.exists():
        raise FileExistsError(f"Refusing to replace an existing delivery: {destination}")
    if destination.is_relative_to(root):
        raise ValueError("Place the exported bundle outside the source repository")
    destination.mkdir(parents=True)
    for item in manifest["files"]:
        target = destination / item["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / item["path"], target)
    shutil.copy2(root / "delivery-manifest.json", destination / "delivery-manifest.json")
    subprocess.run([sys.executable, str(destination / "helpers/verify_delivery.py"), str(destination)],
                   check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--refresh-manifest", action="store_true")
    action.add_argument("--output", type=Path, help="New delivery directory outside the repository")
    args = parser.parse_args()
    manifest = refresh_manifest(ROOT)
    if args.output is not None:
        export_bundle(ROOT, args.output.resolve(), manifest)
    summary = {key: value for key, value in manifest.items() if key != "files"}
    summary["mathematical_verification"] = "existing receipt preserved; Lean not rerun"
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
