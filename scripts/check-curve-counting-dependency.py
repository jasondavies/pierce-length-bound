#!/usr/bin/env python3
"""Check the pinned CCDN dependency metadata, optionally inspecting its checkout.

The pin in lakefile.toml is the single source of truth: lake-manifest.json must resolve
to it, and README.md, formalization.yaml and the paper must cite it. The default check
needs only this repository, so it can run before dependencies are available. Use
--checkout after `lake build` (or `lake update`) to check the fetched source tree in
.lake/packages as well, including that it uses this repository's Lean toolchain and
Mathlib revision.
"""
import argparse
from pathlib import Path
import json
import re
import shlex
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
# Lake requires the [[require]] name to match the package name in CCDN's own lakefile.toml.
DEPENDENCY_NAME = "ccdn_dimension_growth"
DEPENDENCY_URL = "https://github.com/jasondavies/ccdn-dimension-growth"
DEPENDENCY_DIRECTORY = ROOT / ".lake" / "packages" / DEPENDENCY_NAME
FULL_SHA = re.compile(r"[0-9a-f]{40}")
# Files that must cite the full pinned SHA, and any GitHub tree/commit/blob link to CCDN in
# them must use it.
CITING_FILES = ("README.md", "formalization.yaml")
PAPER = Path("paper") / "pierce_length_bound.tex"
CCDN_LINK = re.compile(r"ccdn-(?:linear|dimension)-growth/(?:tree|commit|blob)/([0-9a-f]{7,40})")


def named_entry(entries: list[dict], name: str, location: str) -> dict:
    matches = [entry for entry in entries if entry.get("name") == name]
    if len(matches) != 1:
        raise ValueError(f"{location}: expected exactly one {name} entry, found {len(matches)}")
    return matches[0]


def expect(location: str, field: str, found: object, expected: object) -> None:
    if found != expected:
        raise ValueError(f"{location}: {field} is {found!r}, expected {expected!r}")


def read_metadata(directory: Path) -> tuple[dict, dict]:
    config = tomllib.loads((directory / "lakefile.toml").read_text(encoding="utf-8"))
    manifest = json.loads((directory / "lake-manifest.json").read_text(encoding="utf-8"))
    return config, manifest


def read_toolchain(directory: Path) -> str:
    return (directory / "lean-toolchain").read_text(encoding="utf-8").strip()


def mathlib_revision(config: dict, manifest: dict, location: Path) -> str:
    """Check that the Mathlib requirement and manifest agree; return the resolved SHA."""
    requirement = named_entry(config.get("require", []), "mathlib", f"{location}/lakefile.toml")
    package = named_entry(manifest["packages"], "mathlib", f"{location}/lake-manifest.json")
    manifest_location = f"{location}/lake-manifest.json mathlib"
    expect(manifest_location, "type", package.get("type"), "git")
    expect(manifest_location, "url", package.get("url"), requirement.get("git"))
    expect(manifest_location, "inputRev", package.get("inputRev"), requirement.get("rev"))
    revision = package.get("rev")
    if not isinstance(revision, str) or not FULL_SHA.fullmatch(revision):
        raise ValueError(f"{manifest_location}: rev is {revision!r}, expected a 40-hex SHA")
    return revision


def check_citations(revision: str) -> None:
    for name in CITING_FILES:
        text = (ROOT / name).read_text(encoding="utf-8")
        if revision not in text:
            raise ValueError(f"{name}: does not cite the pinned CCDN commit {revision}")
        for cited in CCDN_LINK.findall(text):
            expect(name, "CCDN link revision", cited, revision)
    paper = (ROOT / PAPER).read_text(encoding="utf-8")
    citation = f"\\lean{{{revision[:7]}}}"
    if citation not in paper:
        found = re.findall(r"commit\s*\\lean\{([0-9a-f]+)\}", paper)
        raise ValueError(f"{PAPER}: cites CCDN commit {found or 'none'}, expected {citation}")


def check_metadata() -> tuple[str, str]:
    """Return the pinned CCDN revision and this repository's Mathlib revision."""
    config, manifest = read_metadata(ROOT)
    requirement = named_entry(config.get("require", []), DEPENDENCY_NAME, "lakefile.toml")
    location = f"lakefile.toml {DEPENDENCY_NAME}"
    if "path" in requirement:
        raise ValueError(f"{location}: must be a Git dependency, not path {requirement['path']!r}")
    expect(location, "git", requirement.get("git"), DEPENDENCY_URL)
    revision = requirement.get("rev")
    if not isinstance(revision, str) or not FULL_SHA.fullmatch(revision):
        raise ValueError(f"{location}: rev is {revision!r}, expected a full 40-hex commit SHA")
    package = named_entry(manifest["packages"], DEPENDENCY_NAME, "lake-manifest.json")
    location = f"lake-manifest.json {DEPENDENCY_NAME}"
    expect(location, "type", package.get("type"), "git")
    expect(location, "url", package.get("url"), DEPENDENCY_URL)
    expect(location, "rev", package.get("rev"), revision)
    expect(location, "inputRev", package.get("inputRev"), revision)
    check_citations(revision)
    return revision, mathlib_revision(config, manifest, ROOT)


def check_checkout(revision: str, mathlib: str) -> None:
    dependency = DEPENDENCY_DIRECTORY
    if not dependency.is_dir():
        raise ValueError(f"CCDN checkout is missing (run lake build first): {dependency}")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=dependency, check=True,
                          capture_output=True, text=True).stdout.strip()
    expect(str(dependency), "checked-out commit", head, revision)
    config, manifest = read_metadata(dependency)
    expect(f"{dependency}/lakefile.toml", "package name", config.get("name"), DEPENDENCY_NAME)
    expect(f"{dependency}/lean-toolchain", "toolchain", read_toolchain(dependency),
           read_toolchain(ROOT))
    expect(f"{dependency}/lake-manifest.json", "Mathlib rev",
           mathlib_revision(config, manifest, dependency), mathlib)
    # Capture only stderr, so that it can be reported on failure; stdout passes through.
    provenance = subprocess.run(
        [sys.executable, str(dependency / "scripts" / "check-provenance.py")],
        cwd=dependency,
        check=True,
        stderr=subprocess.PIPE,
        text=True,
    )
    sys.stderr.write(provenance.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--checkout", action="store_true",
        help="also verify the fetched checkout's revision, toolchain, Mathlib pin, and sources",
    )
    args = parser.parse_args()
    try:
        revision, mathlib = check_metadata()
        if args.checkout:
            check_checkout(revision, mathlib)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Curve-counting dependency check failed: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        print(f"Curve-counting dependency check failed: `{shlex.join(map(str, error.cmd))}` "
              f"exited with status {error.returncode}", file=sys.stderr)
        if error.stderr:
            sys.stderr.write(error.stderr if error.stderr.endswith("\n")
                             else error.stderr + "\n")
        return error.returncode
    print(f"Curve-counting dependency metadata verified: {DEPENDENCY_URL} at {revision}.")
    if args.checkout:
        print("CCDN checkout source checks passed; a Lean build and axiom audit are separate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
