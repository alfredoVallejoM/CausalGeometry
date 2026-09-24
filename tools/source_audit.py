#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "CausalGeometry"
AGGREGATOR = ROOT / "CausalGeometry.lean"

FORBIDDEN = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("axiom", re.compile(r"^\s*axiom\b")),
]


def lean_files() -> list[Path]:
    return sorted([AGGREGATOR, *LEAN_ROOT.rglob("*.lean")])


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if c == "/" and n == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and n == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if in_string:
            if c == "\\":
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if c == "-" and n == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == "/" and n == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if c == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(c)
        i += 1

    return "".join(out)


def proof_hygiene() -> int:
    failures: list[str] = []
    for path in lean_files():
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(stripped.splitlines(), 1):
            for label, pattern in FORBIDDEN:
                if pattern.search(line):
                    rel = path.relative_to(ROOT)
                    failures.append(f"{rel}:{lineno}: forbidden {label}: {line.strip()}")

    workflows = ROOT / ".github" / "workflows"
    if workflows.exists():
        failures.append(".github/workflows exists; project rules forbid GitHub workflows")

    if failures:
        print("[FAIL] proof hygiene")
        for failure in failures:
            print(failure)
        return 1

    print(f"[PASS] proof hygiene: {len(lean_files())} Lean files scanned")
    return 0


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def import_closure() -> int:
    modules = {
        module_name(path)
        for path in LEAN_ROOT.rglob("*.lean")
    }
    imports = set()
    for line in AGGREGATOR.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("import CausalGeometry."):
            imports.add(line.removeprefix("import ").strip())

    missing = sorted(modules - imports)
    stale = sorted(imports - modules)
    if missing or stale:
        print("[FAIL] root import closure")
        for name in missing:
            print(f"missing import: {name}")
        for name in stale:
            print(f"stale import: {name}")
        return 1

    print(f"[PASS] root import closure: {len(modules)} modules imported")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-hygiene", action="store_true")
    parser.add_argument("--imports", action="store_true")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()

    selected = args.all or not (args.proof_hygiene or args.imports)
    results: list[int] = []
    if selected or args.proof_hygiene:
        results.append(proof_hygiene())
    if selected or args.imports:
        results.append(import_closure())
    return 1 if any(results) else 0


if __name__ == "__main__":
    raise SystemExit(main())
