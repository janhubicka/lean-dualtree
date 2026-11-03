# Adversarial audit: nonvacuity of the p-D₀ / q-D₂ height-one mixed span

**3 November 2026 — proposed; Lean CI required before the new lemmas are verified.**

The existence theorem in `PlainBlockBulletBlockRamsey.lean` uses
`span_element_eq_parameterElement`, which only proves the **forward**
representation of points in the source-facing mixed span. By itself this
does not prevent a colour-canonization theorem from becoming vacuous.

This branch adds three explicit source-facing obligations:

1. `parameterElement_mem_span`: every independent tuple
   `σ : Fin p → Fin 1 → β` and `a : Fin q → β` occurs in the actual span.
2. `mixedWord_span_eq_parameter_range`: the genuine span equals precisely
   the full parameter image, not a strict or empty subset.
3. `mixedWord_span_nonempty`: explicit fallback parameters give a point.

The proposed proof uses the actual ray-word evaluation and one variable
per component. The geometric roots of distinct D₂ coordinates coincide
but the substitutions remain independent; no unjustified equality of
observed letters across different q-tuples is assumed.

**Scope limitations.** Only `k=1`, ordered first-p-plain/last-q-bullet
coordinates and no up/D₁ coordinate are covered. The central unproved
work remains arbitrary kind patterns, D₁ leaves, higher intrinsic
height, smooth relative refinements, the repaired Q geometry and
Lemma 27/28 induction. Do not mark Theorem 25/3 as formalized.

**Verification gate.** Require the full Lean umbrella build,
the Q regressions, the source import audit and all 2,111 registered
transitive axiom checks before merging.
