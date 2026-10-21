#!/usr/bin/env python3
"""Check the pinned CCDN dependency metadata, optionally inspecting its checkout.

The default check needs only this repository, so it can run before dependencies
are available. Use --checkout after `lake build` (or `lake update`) to check the
fetched source tree in .lake/packages as well.
"""
import argparse
from pathlib import Path
import json
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCY_NAME = "ccdn_dimension_growth"
DEPENDENCY_URL = "https://github.com/jasondavies/ccdn-linear-growth"
DEPENDENCY_REVISION = "9ade6200d053ceef5f6ccc4154ae30c6056be150"
DEPENDENCY_DIRECTORY = ROOT / ".lake" / "packages" / DEPENDENCY_NAME
LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0"
MATHLIB_REVISION = "56a005855ea17e0b0958f73ec801ae140b0a1679"


def named_entry(entries: list[dict], name: str, location: str) -> dict:
    matches = [entry for entry in entries if entry.get("name") == name]
    if len(matches) != 1:
        raise ValueError(f"{location}: expected exactly one {name} entry")
    return matches[0]


def read_metadata(directory: Path) -> tuple[dict, dict]:
    config = tomllib.loads((directory / "lakefile.toml").read_text(encoding="utf-8"))
    manifest = json.loads((directory / "lake-manifest.json").read_text(encoding="utf-8"))
    return config, manifest


def check_toolchain(directory: Path) -> None:
    toolchain = (directory / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != LEAN_TOOLCHAIN:
        raise ValueError(f"{directory / 'lean-toolchain'}: expected {LEAN_TOOLCHAIN}")


def check_mathlib(config: dict, manifest: dict, location: str) -> None:
    requirement = named_entry(config["require"], "mathlib", f"{location}/lakefile.toml")
    package = named_entry(manifest["packages"], "mathlib", f"{location}/lake-manifest.json")
    if package.get("type") != "git" or package.get("rev") != MATHLIB_REVISION:
        raise ValueError(f"{location}: Mathlib must resolve to {MATHLIB_REVISION}")
    if requirement.get("git") != package.get("url") or requirement.get("rev") != package.get("inputRev"):
        raise ValueError(f"{location}: Mathlib requirement and manifest disagree")


def check_metadata() -> None:
    config, manifest = read_metadata(ROOT)
    requirement = named_entry(config["require"], DEPENDENCY_NAME, "lakefile.toml")
    package = named_entry(manifest["packages"], DEPENDENCY_NAME, "lake-manifest.json")
    if (requirement.get("git") != DEPENDENCY_URL or requirement.get("rev") != DEPENDENCY_REVISION
            or "path" in requirement):
        raise ValueError(
            f"lakefile.toml: {DEPENDENCY_NAME} must be {DEPENDENCY_URL} at {DEPENDENCY_REVISION}")
    if (package.get("type") != "git" or package.get("url") != DEPENDENCY_URL
            or package.get("rev") != DEPENDENCY_REVISION
            or package.get("inputRev") != DEPENDENCY_REVISION):
        raise ValueError("lake-manifest.json: CCDN pin must match lakefile.toml")
    check_toolchain(ROOT)
    check_mathlib(config, manifest, str(ROOT))


def check_checkout() -> None:
    dependency = DEPENDENCY_DIRECTORY
    if not dependency.is_dir():
        raise ValueError(f"CCDN checkout is missing (run lake build first): {dependency}")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=dependency, check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != DEPENDENCY_REVISION:
        raise ValueError(f"{dependency}: checked out {head}, expected {DEPENDENCY_REVISION}")
    config, manifest = read_metadata(dependency)
    if config.get("name") != DEPENDENCY_NAME:
        raise ValueError(f"{dependency}/lakefile.toml: expected package {DEPENDENCY_NAME}")
    check_toolchain(dependency)
    check_mathlib(config, manifest, str(dependency))
    subprocess.run(
        [sys.executable, str(dependency / "scripts" / "check-provenance.py")],
        cwd=dependency,
        check=True,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--checkout", action="store_true",
        help="also verify the fetched checkout's revision, toolchain, Mathlib pin, and sources",
    )
    args = parser.parse_args()
    try:
        check_metadata()
        if args.checkout:
            check_checkout()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Curve-counting dependency check failed: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        return error.returncode
    print(f"Curve-counting dependency metadata verified: {DEPENDENCY_URL} at {DEPENDENCY_REVISION}.")
    if args.checkout:
        print("CCDN checkout source checks passed; a Lean build and axiom audit are separate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
