#!/usr/bin/env python3
"""Regression tests: the source audit must fail closed on silent escapes.

These tests use disposable miniature repositories; they do not modify the
real Lean files or require a Lean installation. Full theorem/axiom checking
remains the job of the separate CI Lean steps.
"""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile

SCRIPT = Path(__file__).with_name("audit-lean-library.py")


def run_case(label: str, bad_module: str | None, extra_module: str | None,
             pass_expected: bool) -> None:
    with tempfile.TemporaryDirectory(prefix="dualtree-audit-") as td:
        root = Path(td)
        (root / "DualTree").mkdir()
        (root / "scripts").mkdir()
        (root / "scripts" / "audit-lean-library.py").write_bytes(
            SCRIPT.read_bytes())
        (root / "DualTree.lean").write_text("import DualTree.Core\n")
        (root / "DualTree" / "Core.lean").write_text(
            "namespace DualTree\ntheorem audited : True := trivial\n"
            + (bad_module or "") + "\nend DualTree\n")
        (root / "scripts" / "CheckDualTree.lean").write_text(
            "#print axioms DualTree.audited\n")
        if extra_module is not None:
            (root / "DualTree" / "Orphan.lean").write_text(extra_module)
        proc = subprocess.run(
            [sys.executable, str(root / "scripts" / "audit-lean-library.py"),
             "--verify-root-minimal"], cwd=root,
            text=True, capture_output=True, check=False)
        if (proc.returncode == 0) != pass_expected:
            raise AssertionError(
                f"{label}: unexpected exit code {proc.returncode}: "
                f"{proc.stdout[-1200:]} {proc.stderr[-1200:]}")


run_case("clean", None, None, True)
run_case("unimported", None, "namespace DualTree\ntheorem orphan : True := trivial\nend DualTree\n", False)
run_case("sorry", "theorem untrusted : True := by sorry", None, False)
run_case("axiom", "axiom injected : True", None, False)
run_case("constant", "constant injected : True", None, False)
run_case("opaque", "opaque injected : True", None, False)
run_case("partial", "partial def looping : Nat → Nat | n => looping n", None, False)
run_case("unsafe", "unsafe def arbitrary : Nat := 0", None, False)
run_case("admit", "theorem untrusted : True := by admit", None, False)
run_case("native_decide", "theorem trivialNative : True := by native_decide", None, False)
print("PASS: source audit rejects missing modules and untrusted declarations")
