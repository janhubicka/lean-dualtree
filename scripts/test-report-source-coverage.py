#!/usr/bin/env python3
"""Miniature repository regressions for the lexical coverage report."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def run_case(remove_required: bool = False, register_extra: bool = True) -> tuple[int, dict]:
    with tempfile.TemporaryDirectory(prefix="dualtree-coverage-") as tmp:
        root = Path(tmp)
        (root / "DualTree").mkdir()
        (root / "scripts").mkdir()
        for name in ("report-source-coverage.py", "audit-lean-library.py"):
            (root / "scripts" / name).write_bytes((HERE / name).read_bytes())
        (root / "DualTree.lean").write_text("import DualTree.Core\n", encoding="utf-8")
        (root / "DualTree" / "Core.lean").write_text(
            """namespace DualTree
namespace InterleavedRamsey
-- theorem commented : False := by sorry
/- theorem alsoCommented : False := by sorry -/
theorem exists_good_interleaved_height_one : True := trivial
private theorem notExported : True := trivial
section S
protected lemma extra : True := trivial
end S
end InterleavedRamsey
end DualTree
namespace DualTree.UpLeafInterleavedCanonical
theorem exists_upCanonical_interleaved_height_one : True := trivial
end DualTree.UpLeafInterleavedCanonical
namespace DualTree.InterleavedColorFactor
theorem good_iff_unique_markerTuple_factor : True := trivial
end DualTree.InterleavedColorFactor
namespace DualTree.ForwardQGlobalHallSpan
theorem exists_full_global_span_iff_hall : True := trivial
end DualTree.ForwardQGlobalHallSpan
namespace DualTree.Corollary22Audit
theorem no_monochromatic_complete_candidate : True := trivial
end DualTree.Corollary22Audit
""", encoding="utf-8")
        endpoints = (
            "DualTree.InterleavedRamsey.exists_good_interleaved_height_one",
            "DualTree.UpLeafInterleavedCanonical.exists_upCanonical_interleaved_height_one",
            "DualTree.InterleavedColorFactor.good_iff_unique_markerTuple_factor",
            "DualTree.ForwardQGlobalHallSpan.exists_full_global_span_iff_hall",
            "DualTree.Corollary22Audit.no_monochromatic_complete_candidate",
        )
        if register_extra:
            endpoints += ("DualTree.InterleavedRamsey.extra",)
        if remove_required:
            endpoints = endpoints[1:]
        (root / "scripts" / "CheckDualTree.lean").write_text(
            "".join(f"#print axioms {e}\n" for e in endpoints), encoding="utf-8")
        output = root / "proof-audit" / "coverage.json"
        proc = subprocess.run(
            [sys.executable, str(root / "scripts" / "report-source-coverage.py"),
             "--json", str(output)], cwd=root, text=True, capture_output=True)
        assert output.is_file(), proc.stdout + proc.stderr
        return proc.returncode, json.loads(output.read_text(encoding="utf-8"))


code, data = run_case()
assert code == 0
assert data["counts"]["lexically_identified_public_theorems"] == 6
assert data["counts"]["identified_private_theorems_excluded"] == 1
assert data["counts"]["identified_public_theorems_unregistered"] == 0
assert not data["unregistered_public_candidates"]
assert not data["parse_warnings"]
code, data = run_case(register_extra=False)
assert code != 0
assert data["counts"]["identified_public_theorems_unregistered"] == 1
assert data["unregistered_public_candidates"][0]["name"] == "DualTree.InterleavedRamsey.extra"
code, data = run_case(remove_required=True)
assert code != 0
assert data["required_not_registered"] == [
    "DualTree.InterleavedRamsey.exists_good_interleaved_height_one"
]
print("PASS: coverage gates checked, unchecked, private and required declarations")
