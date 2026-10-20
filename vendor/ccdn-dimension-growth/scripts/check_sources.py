#!/usr/bin/env python3
"""Verify vendored provenance and that no mathematical source escapes the root import."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "bombieri-vaaler"
metadata = json.loads((VENDOR / "upstream.json").read_text())
expected = metadata["files"] | metadata["patched_files"]
actual = {str(p.relative_to(VENDOR)) for p in (VENDOR / "ArithmeticHeights").rglob("*.lean")}
if actual != set(expected):
    raise SystemExit("Vendored file inventory differs from the provenance manifest")
for relative, digest in expected.items():
    if hashlib.sha256((VENDOR / relative).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Vendored source hash mismatch: {relative}")

mertens = json.loads((ROOT / "vendor" / "mertens" / "upstream.json").read_text())
if hashlib.sha256((ROOT / "AffineCurveCounting" / "MertensFirst.lean").read_bytes()).hexdigest() != mertens["adapted_sha256"]:
    raise SystemExit("Adapted Mertens source differs from the provenance manifest")

modules = {
    ".".join(p.relative_to(ROOT).with_suffix("").parts): p
    for p in (ROOT / "AffineCurveCounting").rglob("*.lean")
}
modules["AffineCurveCounting"] = ROOT / "AffineCurveCounting.lean"
modules.update({
    ".".join(p.relative_to(VENDOR).with_suffix("").parts): p
    for p in (VENDOR / "ArithmeticHeights").rglob("*.lean")
})
seen = set()

def visit(name):
    if name in seen:
        return
    seen.add(name)
    for dep in re.findall(r"^(?:public )?import (?:all )?(\S+)", modules[name].read_text(), re.M):
        if dep in modules:
            visit(dep)
        elif dep.startswith(("AffineCurveCounting", "ArithmeticHeights")):
            raise SystemExit(f"Missing project dependency: {dep}")

visit("AffineCurveCounting")
missing = set(modules) - seen
if missing:
    raise SystemExit(f"Mathematical sources omitted from build/audit: {sorted(missing)}")
print(f"Source checks passed: {len(expected)} vendor hashes; {len(seen)} reachable modules.")
