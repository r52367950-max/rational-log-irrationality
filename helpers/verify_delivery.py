#!/usr/bin/env python3
"""Verify a delivered source bundle's hashes, import-only changes and axiom records.

This is an integrity check; rerun Lean separately to check mathematical proofs.
Usage from the extracted bundle: python helpers/verify_delivery.py .
"""
import hashlib
import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
manifest = json.loads((root / "delivery-manifest.json").read_text())
assert manifest["file_count"] == len(manifest["files"])
assert manifest["total_source_bytes"] == sum(entry["bytes"] for entry in manifest["files"])
assert len({entry["path"] for entry in manifest["files"]}) == len(manifest["files"])
for entry in manifest["files"]:
    path = (root / entry["path"]).resolve()
    assert path.is_relative_to(root), entry["path"]
    data = path.read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

provenance = json.loads((root / "oai017-upstream/source-provenance.json").read_text())
def body(data):
    return re.sub(rb"(?m)^import [^\r\n]*\r?\n", b"", data)
for entry in provenance["files"]:
    pristine = (root / "oai017-upstream" / entry["path"]).read_bytes()
    working = (root / "lean-oai017/portable_project" / entry["path"]).read_bytes()
    assert hashlib.sha256(pristine).hexdigest() == entry["sha256"], entry["path"]
    blob = b"blob " + str(len(pristine)).encode() + b"\0" + pristine
    assert hashlib.sha1(blob).hexdigest() == entry["git_blob_sha"], entry["path"]
    assert body(pristine) == body(working), entry["path"]

permitted = {"propext", "Classical.choice", "Quot.sound"}
counts = {}
for project in ["local", "oai017"]:
    entries = json.loads((root / f"checks/lean-{project}-theorem-axioms.json").read_text())
    assert len({item["theorem"] for item in entries}) == len(entries)
    assert all(set(item["axioms"]) <= permitted for item in entries)
    counts[project] = len(entries)
assert manifest["main_status"] == "complete_main_formalization"
receipt = json.loads((root / "checks/final-main-receipt.json").read_text())
assert receipt["status"] == "accepted"
assert all(receipt[k] is True for k in ["independent_reference_graph_match", "exact_type_match",
    "fresh_builtin_kernel_dependency_replay", "kernel_statement_certificate_checked"])
assert receipt["candidate"] == manifest["main_candidate"]
print(json.dumps({"hashes":"passed", "upstream_modules":len(provenance["files"]),
    "proof_body_changes":0, "axiom_records":counts,
    "main_theorem_status":manifest["main_status"]}, ensure_ascii=False, indent=2))
