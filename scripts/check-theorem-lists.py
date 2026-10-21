#!/usr/bin/env python3
"""Check that every list of the selected theorems matches comparator.json, in order.

comparator.json `theorem_names` is the source of truth and must be nonempty. The same
names, in the same order, must be the `theorem` declarations of the Challenge module, the
first `#print axioms` checks in Axioms.lean, the `lean` entries of the formalization.yaml
alignment, and the theorems in the first Lean code block after README.md's "Main theorem
statements" heading (at any heading level).
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# A theorem name ends at the first whitespace, colon or binder opener.
THEOREM = re.compile(r"^theorem\s+([^\s:({\[]+)", re.MULTILINE)
NAMESPACE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)
# The expected message names the declaration in full; `#print axioms` may abbreviate it.
AXIOM_CHECK = re.compile(
    r"/-- info: '([^']+)' depends on axioms:.*?-/\s*#guard_msgs in\s*#print axioms (\S+)",
    re.DOTALL,
)
ALIGNMENT_LEAN = re.compile(r"^\s+lean:\s*\"?([^\"\s]+)\"?\s*$", re.MULTILINE)
README_HEADING = re.compile(r"^#+\s+Main theorem statements\s*$", re.MULTILINE)
README_LEAN_BLOCK = re.compile(r"^```lean\n(.*?)^```", re.MULTILINE | re.DOTALL)


def challenge_theorems(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    namespaces = NAMESPACE.findall(text)
    if len(namespaces) != 1:
        raise ValueError(f"{path.name}: expected one namespace, found {namespaces}")
    return [f"{namespaces[0]}.{name}" for name in THEOREM.findall(text)]


def axiom_checks(path: Path) -> list[str]:
    names = []
    for full, target in AXIOM_CHECK.findall(path.read_text(encoding="utf-8")):
        if not (full == target or full.endswith("." + target)):
            raise ValueError(f"{path.name}: #print axioms {target} expects a message for {full}")
        names.append(full)
    return names


def alignment_entries(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    start = re.search(r"^alignment:\s*$", text, re.MULTILINE)
    if start is None:
        raise ValueError(f"{path.name}: no alignment section")
    end = re.search(r"^\S", text[start.end():], re.MULTILINE)
    section = text[start.end():start.end() + end.start()] if end else text[start.end():]
    return ALIGNMENT_LEAN.findall(section)


def readme_theorems(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    heading = README_HEADING.search(text)
    if heading is None:
        raise ValueError(f"{path.name}: no \"Main theorem statements\" heading")
    block = README_LEAN_BLOCK.search(text, heading.end())
    if block is None:
        raise ValueError(f"{path.name}: no ```lean block after \"Main theorem statements\"")
    return THEOREM.findall(block.group(1))


def main() -> int:
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    expected = config["theorem_names"]
    if not isinstance(expected, list) or not expected:
        raise ValueError("comparator.json: theorem_names must be a nonempty list")
    challenge = ROOT / (config["challenge_module"].replace(".", "/") + ".lean")
    lists = {
        challenge.name + " theorems": challenge_theorems(challenge),
        "Axioms.lean first #print axioms checks":
            axiom_checks(ROOT / "Axioms.lean")[:len(expected)],
        "formalization.yaml alignment": alignment_entries(ROOT / "formalization.yaml"),
        "README.md main theorem statements": readme_theorems(ROOT / "README.md"),
    }
    failed = False
    for source, found in lists.items():
        if found != expected:
            index = next((i for i, (f, e) in enumerate(zip(found, expected)) if f != e),
                         min(len(found), len(expected)))
            print(f"{source} does not match comparator.json theorem_names at position "
                  f"{index + 1}: found {found[index:index + 1] or 'end of list'}, expected "
                  f"{expected[index:index + 1] or 'end of list'} ({len(found)} vs "
                  f"{len(expected)} names)", file=sys.stderr)
            failed = True
    if not failed:
        print(f"Theorem lists match comparator.json ({len(expected)} theorems).")
    return int(failed)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError) as error:
        print(f"Theorem-list check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
