#!/usr/bin/env python3
"""Static, conservative audit of the lean-dualtree source and import graph.

This is an aid to adversarial review, NOT an assertion that all definitions
are mathematically faithful to the source paper, and NOT a replacement for
the Lean kernel or the source-facing transitive #print axioms audit.

--check: print a reproducible diagnostic report, without modifying files.
--compact-root: remove *provably transitively redundant direct imports*
                in DualTree.lean; retain the same transitive module closure.
--verify-root-minimal: fail if DualTree.lean has transitive duplicate imports.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path
import re
import sys

REPO = Path(__file__).resolve().parents[1]
ROOT = REPO / "DualTree.lean"
PREFIX = "DualTree."


def strip_comments(source: str) -> str:
    """Remove nested Lean /- ... -/ and -- comments; keep line boundaries.

    Strings are kept verbatim. We do not treat strings as code, so this is
    a conservative lexical diagnostic rather than a verified Lean parser.
    """
    out: list[str] = []
    i = 0
    nesting = 0
    in_string = False
    while i < len(source):
        if nesting:
            if source.startswith("/-", i):
                nesting += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                nesting -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            elif source[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue
        if source.startswith("/-", i):
            nesting = 1
            out.extend("  ")
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def load() -> tuple[dict[str, str], dict[str, list[str]]]:
    paths = [ROOT, *sorted((REPO / "DualTree").rglob("*.lean"))]
    texts: dict[str, str] = {}
    imports: dict[str, list[str]] = {}
    for path in paths:
        mod = ".".join(path.relative_to(REPO).with_suffix("").parts)
        source = path.read_text(encoding="utf-8")
        texts[mod] = source
        cleaned = strip_comments(source)
        imported: list[str] = []
        for line in cleaned.splitlines():
            m = re.match(r"^\s*import\s+(.+?)\s*$", line)
            if m:
                imported.extend(m.group(1).split())
        imports[mod] = imported
    return texts, imports


def reachable(imports: dict[str, list[str]], starts: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(starts)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(d for d in imports.get(mod, []) if d in imports)
    return seen


def minimal_root_imports(imports: dict[str, list[str]]) -> tuple[list[str], list[str]]:
    original = imports["DualTree"]
    # Import DAG: a direct import is redundant exactly when another directly
    # imported module transitively imports it. The module can then be removed
    # from the root import list without altering root's transitive closure.
    essential: list[str] = []
    redundant: list[str] = []
    for idx, dep in enumerate(original):
        others = original[:idx] + original[idx + 1:]
        if dep in reachable(imports, others):
            redundant.append(dep)
        else:
            essential.append(dep)
    assert reachable(imports, essential) == reachable(imports, original)
    return essential, redundant


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--compact-root", action="store_true")
    parser.add_argument("--verify-root-minimal", action="store_true")
    args = parser.parse_args()
    texts, imports = load()
    original = imports["DualTree"]
    essential, redundant = minimal_root_imports(imports)
    source_mods = set(texts) - {"DualTree"}
    reached = reachable(imports, original)
    missed = sorted(source_mods - reached)
    external = Counter(x for deps in imports.values() for x in deps
                       if x not in texts)
    inbound: dict[str, set[str]] = defaultdict(set)
    for src, deps in imports.items():
        for dep in deps:
            if dep in texts:
                inbound[dep].add(src)
    only_root = sorted(m for m in source_mods if inbound[m] == {"DualTree"})

    checked = (REPO / "scripts/CheckDualTree.lean").read_text(encoding="utf-8")
    counted = len(re.findall(r"(?m)^\s*#print axioms\s+", checked))
    prohibited: dict[str, list[str]] = {}
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "axiom": r"(?m)^\s*(?:private\s+)?axiom\b",
        "opaque": r"(?m)^\s*(?:private\s+)?opaque\b",
        "unsafe": r"(?m)^\s*(?:private\s+)?unsafe\b",
        "native_decide": r"\bnative_decide\b",
    }
    for label, pattern in patterns.items():
        matches = [mod for mod, text in texts.items()
                   if re.search(pattern, strip_comments(text))]
        prohibited[label] = matches
    private_candidates: list[str] = []
    all_clean = "\n".join(strip_comments(s) for s in texts.values())
    for mod, source in texts.items():
        for match in re.finditer(
                r"(?m)^\s*private\s+(?:theorem|lemma|def|abbrev)\s+([A-Za-z_]\w*)",
                strip_comments(source)):
            name = match.group(1)
            # Safe diagnostic only: unqualified name occurrences can be
            # shadowed, and tactic-generated references are not recorded.
            if len(re.findall(r"\b" + re.escape(name) + r"\b", all_clean)) == 1:
                private_candidates.append(f"{mod}.{name}")

    print(f"AUDIT_LEAN_MODULES {len(texts)}")
    print(f"AUDIT_ROOT_DIRECT_IMPORTS {len(original)}")
    print(f"AUDIT_ROOT_ESSENTIAL_IMPORTS {len(essential)}")
    print(f"AUDIT_ROOT_TRANSITIVELY_REDUNDANT {len(redundant)}")
    print(f"AUDIT_ROOT_CLOSURE {len(reached)}")
    print(f"AUDIT_UNREACHABLE_SOURCE_MODULES {len(missed)}")
    print(f"AUDIT_ONLY_ROOT_IMPORTERS {len(only_root)}")
    print(f"AUDIT_AXIOM_REPORTS_REGISTERED {counted}")
    for label, matches in prohibited.items():
        print(f"AUDIT_LEXICAL_{label.upper()} {len(matches)}")
        if matches:
            print(f"AUDIT_LEXICAL_{label.upper()}_MODULES "
                  + " ".join(matches[:25]))
    print(f"AUDIT_UNUSED_PRIVATE_CANDIDATES {len(private_candidates)}")
    if private_candidates:
        print("AUDIT_PRIVATE_CANDIDATES " + " ".join(private_candidates[:35]))
    if missed:
        print("AUDIT_UNREACHABLE_MODULES " + " ".join(missed))
    if redundant:
        print("AUDIT_REDUNDANT_ROOT_MODULES " + " ".join(redundant))
    print("AUDIT_ESSENTIAL_ROOT_MODULES " + " ".join(essential))
    print("AUDIT_EXTERNAL_IMPORT_NAMES " + " ".join(sorted(external)[:30]))
    # Exact suspects for replacing now-obsolete scaffolding with the
    # genuine fibrewise starred Q output. Report source-module references
    # before editing a declaration or subtracting its audited endpoint.
    for name in (
        "placeholderStarredWordOnQ",
        "placeholderStarredWordOnQ_tree",
        "retained_source_word_witness",
        "retained_source_word_witness_tree",
    ):
        refs = sorted(
            mod for mod, source in texts.items()
            if re.search(r"\b" + re.escape(name) + r"\b", strip_comments(source))
        )
        print("AUDIT_SUSPECT_REFERENCES " + name + " " + " ".join(refs))

    if args.compact_root:
        current = ROOT.read_text(encoding="utf-8")
        content_lines = [line for line in strip_comments(current).splitlines()
                         if line.strip() and not re.match(r"^\s*import\s+", line)]
        if content_lines:
            raise SystemExit(
                "Refusing to rewrite a root file with non-import code: "
                + repr(content_lines[:5]))
        compact = (
            "/-!\n"
            "Public umbrella import for the dual-tree verification library.\n"
            "Imports below form a minimal transitive covering of all original\n"
            "source modules. Run scripts/audit-lean-library.py --check to\n"
            "recompute the graph; individual module files remain independently\n"
            "importable. Audit/counterexample modules remain exported.\n"
            "-/\n\n" + "\n".join(f"import {mod}" for mod in essential) + "\n"
        )
        ROOT.write_text(compact, encoding="utf-8")
        print(f"AUDIT_COMPACT_ROOT_SAVED {ROOT}")
    if args.verify_root_minimal and redundant:
        print("FAIL: transitive duplicate root imports", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
