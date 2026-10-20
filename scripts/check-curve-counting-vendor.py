#!/usr/bin/env python3
"""Verify the pinned curve-counting source snapshot and its nested provenance."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "ccdn-dimension-growth"
metadata = json.loads((VENDOR / "upstream.json").read_text())
expected = metadata["files"]
actual = {
    str(p.relative_to(VENDOR))
    for p in VENDOR.rglob("*")
    if p.is_file()
    and not any(part in {".lake", ".git"} for part in p.relative_to(VENDOR).parts)
    and p.relative_to(VENDOR) not in {Path("upstream.json"), Path("UPSTREAM.md")}
}
if actual != set(expected):
    raise SystemExit("Curve-counting snapshot inventory mismatch")
for relative, digest in expected.items():
    p = VENDOR / relative
    if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Curve-counting snapshot hash mismatch: {relative}")
    if p.suffix == ".lean" and digest != metadata["source_files"][relative]:
        raise SystemExit(f"Mathematical source differs from audited source: {relative}")
inventory_digest = hashlib.sha256(
    json.dumps(metadata["source_files"], sort_keys=True, separators=(",", ":")).encode()
).hexdigest()
if inventory_digest != metadata["source_worktree_snapshot_sha256"]:
    raise SystemExit("Curve-counting source inventory digest mismatch")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
if mathlib["rev"] != metadata["verification"]["mathlib_commit"]:
    raise SystemExit("Parent Mathlib differs from the audited curve-counting toolchain")
subprocess.run([sys.executable, str(VENDOR / "scripts" / "check_sources.py")], check=True)
print(f"Curve-counting snapshot verified: {len(expected)} files; {inventory_digest}.")
