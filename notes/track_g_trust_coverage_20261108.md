# Track G — independent trust and source-contract checkpoint

**Date:** 8 November 2026. **Source basis:** main commit
4d7879863c8725a92344c4d26ae8b48414f04811, reached after Track B
merges #533, #535, #537, #539 and coordination #521.
This main tree contains 467 Lean files beneath DualTree/ and 2,352
registered #print axioms declarations. At inspection the newest main
Lean workflow was *queued*, not finished. Earlier successful checks
do **not** certify this commit.

This checkpoint is **not** a line-by-line mathematical verification,
an assertion that the published main theorem is true as printed,
or an inference of completion percentage from registry size.

## New independent coverage gate

The script scripts/report-source-coverage.py scans straightforward
named theorem/lemma commands in every DualTree/*.lean file, maintaining
lexical namespace/section scope and excluding explicitly private
declarations. It compares reconstructed names to
scripts/CheckDualTree.lean and emits machine-readable JSON including
unmatched candidate declarations, source module, line number, and
scope warnings. It requires continued registration of five high-value
interfaces below. Regression tests use disposable miniature
repositories and fail when a required registered endpoint is removed.
The Lean Source Audit workflow runs the tests and scan on library changes.

**Limits:** this is a lexical name comparison, *not* a Lean parser.
Nested syntax, quoted names, generated declarations and some private
or scoped naming may escape enumeration; registered definitions are
reported outside the theorem subset rather than falsely marked as
missing source. A registered name does **not** ensure a theorem has the
published quantifiers, is mathematically the desired assertion, or
has only standard axioms. Full Lean compilation, transitive axiom
checking and source-to-paper correspondence review remain mandatory.
Unregistered public-name candidates are a review queue, **not** a
claim that these theorems are unproved.

## Focused statement-to-Lean audit

All names below are literal declarations on the stated main baseline,
and all five occur in its transitive-axiom register. This checks
statement scope, not paper-level proof completeness.

1. **D0/D2 positive height-one existence.**
   DualTree.InterleavedRamsey.exists_good_interleaved_height_one,
   in DualTree/InterleavedRamsey.lean. Hypotheses:
   0 < b, arbitrary coordinate-kind map kind : Fin d → CoordKind,
   NoUp kind, finite alphabets β and γ, and a genuine
   fallback : β. Conclusion has quantifier order
   ∃ n, ∀ color : Element b n d β kind → γ, ∃ f of intrinsic
   height 1 with MixedProduct.Good color f.
   This handles D0/D2 interleavings, but neither D1 nor k ≥ 2
   nor relative refinements. fallback : β excludes the truly empty
   alphabet case.

2. **D1 canonicalization does not imply Definition-11 Good.**
   DualTree.UpLeafInterleavedCanonical.exists_upCanonical_interleaved_height_one,
   in DualTree/UpLeafInterleavedCanonical.lean after PR #539.
   Hypotheses: 0 < b, NoBullet kind, finite β/γ and fallback : β.
   Quantifier order: ∃ n, ∀ color, ∃ f.
   Conclusion: f.span.Nonempty ∧ UpCanonical color f.
   It does **not** state Good color f: the ambient trace retains
   D1 direction/root-letter information. Treating it as the full
   mixed D1 Ramsey theorem would silently remove a real condition.

3. **Retained marker observations are not erased.**
   DualTree.InterleavedColorFactor.good_iff_unique_markerTuple_factor,
   in DualTree/InterleavedColorFactor.lean, works under NoUp kind
   and the constructed height-one interleaved word. Good is
   equivalent to color factorization through the full tuple of
   actual D2 observed letters, with a **unique total** factor thanks
   to exact nonempty-span coverage. It does not equate different
   marker tuples or establish Γ1 residual-color constancy.

4. **Global Hall condition is an assumption to prove, not free.**
   DualTree.ForwardQGlobalHallSpan.exists_full_global_span_iff_hall,
   in DualTree/ForwardQGlobalHallSpan.lean. The equivalence for a
   fixed Q frame and raw tagged local words assumes both
   SpanAudit.HasTwoLetters β and EveryTagOccursInCone c q raw.
   The right side is the full HallCondition c q over **all**
   subsets of tagged variables. It neither constructs local
   Ramsey words nor establishes Hall automatically. Independent
   local frontier capacity bounds do not suffice when source-root
   sets overlap.

5. **Corollary 22 obstruction is localized.**
   DualTree.Corollary22Audit.no_monochromatic_complete_candidate,
   in DualTree/Corollary22Audit.lean, proves the height-one Boolean
   obstruction for a specified complete support. This does not
   kernel-check the globally quantified MTHJ/CT numerical wrapper.

## Nonimplications to preserve as regression obligations

- Printed reverse-lex Q and naive reindexing have typed
  counterexamples. Forward order uses a corrected starred domain;
  there is no general printed-domain equivalence theorem.
- Over a one-letter alphabet evaluated-span containment cannot
  observe variable support. The theorem needs suitable syntactic
  refinement or nondegeneracy.
- Smoothness retains Γ1 letters and marked-point information.
  Neither Good nor UpCanonical establishes across-record constancy.
- Forward Q image coverage does not imply reverse span inclusion.
  Fixed auxiliary constants in the enlarged alphabet add a separate
  obstruction to transfer.
- Lemma 27's printed tail domains, surjection, occurrence-based
  substitution and global Hall matching require corrected checks.
  Conditional interfaces alone do not discharge these claims.
- Lemmas 27–28 and Theorems 25, 3 and 29 still need final
  integration and exact quantitative/source assumptions.
  The dual-tree Ramsey theorem remains uncertified.

## Next independent audit priorities

1. Review the JSON's unmatched **public theorem candidates**,
   beginning with major existential theorems and counterexample
   fixtures; do not interpret declaration counts as completion.
2. Adversarially compare new C/D/E/F theorem signatures with
   paper statements (quantifier order, D1/D2 records, source-vs-forward
   Q domain, alphabet nondegeneracy, nonvacuity, Hall premises).
3. Remove suspected dead code only after import/reference analysis,
   source audit, complete Lean compilation, all finite regressions
   and full transitive-axiom checking. This change removes no
   mathematical source code.

Historical evidence and scope:
notes/parallel_validation_tracks_20261104.md and
notes/adversarial_full_audit_20261029.md.
