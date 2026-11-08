#!/usr/bin/env python3
"""Conservative lexical theorem/registry coverage report for lean-dualtree.

Coverage here means name correspondence to a registered #print axioms
command, NOT proof completeness, semantic fidelity, or a Lean parser result.
All reports are reproducible from checkout contents; the full Lean build and
transitive axiom log remain mandatory independent trust gates.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import json
import re
import runpy

REPO = Path(__file__).resolve().parents[1]
STRIP = runpy.run_path(str(Path(__file__).with_name("audit-lean-library.py")))["strip_comments"]
PRINT = re.compile(r"(?m)^\s*#print\s+axioms\s+([A-Za-z0-9_.'\u00ab\u00bb]+)\s*$")
# Lexical, deliberately conservative. Quoted identifiers, syntax-generated
# declarations and non-command theorems require an actual Lean environment.
NAME = r"[A-Za-z_][\w.']*"
OPEN = re.compile(rf"^\s*namespace\s+({NAME})\s*$")
SECTION = re.compile(rf"^\s*(?:noncomputable\s+)?section(?:\s+({NAME}))?\s*$")
MUTUAL = re.compile(r"^\s*mutual\s*$")
END = re.compile(rf"^\s*end(?:\s+({NAME}))?\s*$")
DECL = re.compile(
    rf"^\s*(?:@\[[^]]*\]\s*)*"
    rf"(?P<mods>(?:(?:private|protected|noncomputable|local|scoped|public)\s+)*)"
    rf"(?P<kind>theorem|lemma)\s+(?P<name>{NAME})(?=\s|$|[(:{{\[])"
)
UNNAMED = re.compile(r"^\s*(?:theorem|lemma)\s*(?::|\()")

# The five high-value interfaces below MUST remain in the explicit registry.
# Their precise hypotheses and limitations are documented in the Track G note.
REQUIRED = (
    "DualTree.InterleavedRamsey.exists_good_interleaved_height_one",
    "DualTree.UpLeafInterleavedCanonical.exists_upCanonical_interleaved_height_one",
    "DualTree.InterleavedColorFactor.good_iff_unique_markerTuple_factor",
    "DualTree.ForwardQGlobalHallSpan.exists_full_global_span_iff_hall",
    "DualTree.Corollary22Audit.no_monochromatic_complete_candidate",
)


def candidates(path: Path) -> tuple[list[dict[str, object]], list[str]]:
    """Parse only top-level, simply named theorem/lemma declarations.

    Namespace and section/end pairing are tracked, but this is NOT intended to
    reproduce Lean's full name resolution (especially private or macros).
    """
    clean = STRIP(path.read_text(encoding="utf-8"))
    scope: list[tuple[str, str | None]] = []
    out: list[dict[str, object]] = []
    warnings: list[str] = []
    module = ".".join(path.relative_to(REPO).with_suffix("").parts)
    for line_number, line in enumerate(clean.splitlines(), 1):
        if match := OPEN.match(line):
            scope.append(("namespace", match.group(1)))
            continue
        if match := SECTION.match(line):
            scope.append(("section", match.group(1)))
            continue
        if MUTUAL.match(line):
            scope.append(("mutual", None))
            continue
        if match := END.match(line):
            if scope:
                actual_kind, actual_name = scope.pop()
                expected = match.group(1)
                if expected is not None and expected != actual_name:
                    warnings.append(f"{module}:{line_number}: end {expected} closes {actual_kind} {actual_name}")
            else:
                warnings.append(f"{module}:{line_number}: unmatched end command")
            continue
        match = DECL.match(line)
        if match:
            modifiers = match.group("mods").split()
            name = match.group("name")
            prefix = [s for kind, n in scope if kind == "namespace" and n for s in n.split(".")]
            full_name = ".".join([*prefix, name])
            out.append({
                "name": full_name,
                "module": module,
                "line": line_number,
                "kind": match.group("kind"),
                "private": "private" in modifiers,
            })
        elif UNNAMED.match(line):
            warnings.append(f"{module}:{line_number}: unclassified theorem/lemma syntax")
    return out, warnings


def report() -> tuple[dict[str, object], list[str]]:
    source_files = sorted((REPO / "DualTree").rglob("*.lean"))
    registered = PRINT.findall((REPO / "scripts/CheckDualTree.lean").read_text(encoding="utf-8"))
    reg_set = set(registered)
    declarations: list[dict[str, object]] = []
    warnings: list[str] = []
    for path in source_files:
        ds, ws = candidates(path)
        declarations.extend(ds)
        warnings.extend(ws)
    public = [d for d in declarations if not d["private"]]
    registered_public = [d for d in public if d["name"] in reg_set]
    not_registered = [d for d in public if d["name"] not in reg_set]
    # Registered definitions, generated constructors and names outside our
    # lexical subset are *not* wrongly classified as missing source files.
    public_names = {d["name"] for d in public}
    elsewhere = sorted(reg_set - public_names)
    by_module: dict[str, dict[str, int]] = defaultdict(lambda: {"identified": 0, "registered": 0})
    for d in public:
        by_module[str(d["module"])]["identified"] += 1
        by_module[str(d["module"])]["registered"] += int(d["name"] in reg_set)
    missing_required = sorted(set(REQUIRED) - reg_set)
    parsed_required = sorted(set(REQUIRED) - public_names)
    duplicates = sorted({name for name in reg_set if registered.count(name) > 1})
    counts = {
        "source_modules": len(source_files),
        "registered_endpoints": len(registered),
        "registered_endpoints_distinct": len(reg_set),
        "lexically_identified_public_theorems": len(public),
        "identified_public_theorems_registered": len(registered_public),
        "identified_public_theorems_unregistered": len(not_registered),
        "identified_private_theorems_excluded": len(declarations) - len(public),
        "registered_endpoints_outside_public_theorem_subset": len(elsewhere),
        "scope_warnings": len(warnings),
    }
    result = {
        "method": "Lexical named theorem/lemma scanner; not a Lean parser or a mathematical proof audit.",
        "counts": counts,
        "required_source_interfaces": list(REQUIRED),
        "required_not_registered": missing_required,
        "required_not_parsed": parsed_required,
        "duplicate_registry_endpoints": duplicates,
        "modules": dict(sorted(by_module.items())),
        "unregistered_public_candidates": sorted(not_registered, key=lambda d: (d["module"], d["line"])),
        "registered_non_theorem_endpoints": elsewhere,
        "parse_warnings": warnings,
    }
    failures = []
    if missing_required:
        failures.append("missing required registered interfaces: " + ", ".join(missing_required))
    if parsed_required:
        failures.append("required source interfaces not recognized by scanner: " + ", ".join(parsed_required))
    if duplicates:
        failures.append("duplicate registered endpoints: " + ", ".join(duplicates))
    return result, failures


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", type=Path, help="Write complete reproducible report (including unregistered names)")
    args = ap.parse_args()
    data, failures = report()
    for key, value in data["counts"].items():
        print(f"COVERAGE_{key.upper()} {value}")
    print("COVERAGE_METHOD lexical-name-match-not-mathematical-verification")
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"COVERAGE_JSON {args.json}")
    if failures:
        for failure in failures:
            print("FAIL: " + failure)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
