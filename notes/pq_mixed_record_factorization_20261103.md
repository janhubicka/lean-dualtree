# Canonical q-marker colour factorization for the p-D₀/q-D₂ height-one base

**3 November 2026 — proposed Lean module, pending CI at submission.**

The merged exact span theorem is much stronger than a sufficient c-goodness
criterion. The forward and converse span representations allow us to prove
that the Definition-11 c-good predicate for the genuine p/q ray mixed word
is **equivalent**, not merely implied by, finite-parameter Hales–Jewett
fibre constancy.

Define the actual observation map `markerTuple x` from q independent
D₂ bullet coordinates to their genuine observed letters. Each parameter
element has `markerTuple = a`; conversely all q-tuples are realized, by
the exact mixed-span theorem. This yields

```
  Good color f ↔ ∃ F : (Fin q → β) → γ,
    ∀ x ∈ f.span, color x = F (markerTuple x).
```

The total factor F is unique. This includes p=0, q=0, and cases with a
singleton original alphabet, provided the original fallback letter is
supplied. The result does **not** identify the different q-letter tuples,
which would be false for a colouring that reads the D₂ observations.

**Adversarial scope check.** This is a local fibre-factorization interface
at k=1 in the ordered D₀/D₂ block case, not an induction theorem or a
proof of Definition-21 smoothness. It does not solve D₁ leaf selection,
interleaved coordinate kinds, higher-dimensional complete-skew words,
the corrected Q source/refinement issue, Lemma 27 or Theorem 3.

Require the complete Lean umbrella, finite regressions, minimal-import
audit and 2,116 transitive axiom reports before merging.
