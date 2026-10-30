# Finite Hales–Jewett existence imported into DualTree's word API

**30 October 2026.** Mathlib already contains a kernel-checked
multidimensional Hales–Jewett theorem; this note records its
precise connection to the DualTree formalization and what still
prevents it from proving Theorem 13 or the dual-tree theorem.

## The genuine flat existence theorem (#476)

Mathlib's
`Combinatorics.Subspace.exists_mono_in_high_dimension_fin`
proves that, given finite alphabet `β`, finite colour type `γ`
and finite variable type `η`, some finite `N` has a
monochromatic *proper* combinatorial subspace of
`Fin N → β` under every `γ`-colouring.

Its word representation is a function
`l.idxFun : Fin N → Sum β η`, with `l.proper` asserting that
every variable in `η` actually occurs. This is exactly the
constant/variable structure of our own
`DualTree.SpanAudit.eval`, not just an informal analogy.

The file `DualTree/FlatHalesJewett.lean` proves:
- `subspace_eval_eq`: exact equality of the Mathlib
  `Subspace` evaluation and `SpanAudit.eval`;
- `subspace_span_eq_range`: equality of the *entire*
  evaluated span with the subspace's parametrized range;
- `exists_monochromatic_flat_word`: for arbitrary finite
  `β, γ` and `k`, some finite `N` makes every colouring
  of `Fin N → β` monochromatic on the span of a genuine
  `Fin k`-variable word, every variable occurring;
- `exists_monochromatic_flat_span`: the same result
  phrased directly as monochromaticity on
  `SpanAudit.span w`.

This is **actual finite Ramsey existence** deduced from a
proved theorem, not an assumed `hgood` or `hmono` about
an arbitrarily chosen local word. No implicit numerical
bounds are claimed: Mathlib provides an existential `N`.

## A synchronized flat vector theorem (#477)

The file `DualTree/FlatVectorHalesJewett.lean`
applies the above theorem to the finite PRODUCT alphabet
`Fin d → β` and projects each constant vector letter
to its coordinate.

The same variable index occurs at exactly the same
joint-word positions in every coordinate, but the
substitution `σ : Fin d → Fin k → β` may choose its
values independently in all d coordinates. Therefore this
is a true monochromatic *rectangular vector product*,
not a diagonal one-parameter family. The formal
results are:
- `coordinate_eval` (the exact product-to-coordinate
  substitution identity);
- `coordinate_occurs_of_proper` (each variable occurs
  simultaneously across all vector coordinates);
- `exists_monochromatic_flat_vector` (one finite N
  works for every colouring of the whole vector word
  hypercube, with ALL independent coordinate assignments).

## The unresolved geometric bridge is substantial

`SpanAudit` is a completely flat word theory. Nothing
in ordinary Hales–Jewett guarantees that the variable
root support of a tree-indexed word is a k-complete
skew subtree, let alone that a vector of such supports
is vector-complete skew. The theorem does NOT construct:
- a root-aligned `VariableWord b n β` satisfying the
  paper's `atRoot` and `below` conditions;
- a `KVariableWord` with k-complete skew support;
- a vector `MixedProduct.VectorVariableWord` with
  `VectorSkew.vectorCompleteB`;
- the required D₁ up-leaf sets or D₂ selected
  marked-root supports and starred ordering;
- the full mixed-product `Good` witness, its
  quantitative dimension bounds, or smoothness
  required for the corrected Lemma 27.

The true next mathematical obligation is a
**tree-compatible block/partite construction** that
preserves all those support conditions while importing
the flat Hales–Jewett colour canonization. It must not
assume the false Corollary-22 conclusion that the
complete Γ₁ residual record itself becomes constant.

## Connection to the corrected colour-record induction

Merged PRs #472–474 already prove:
- the Γ₁ reduced record itself is NOT constant on
  the full positive-dimensional enlarged starred
  mixed span when Γ₁ contains a selected D₂ index;
- for a globally smooth colouring c-good on a
  genuine local word, its colour factors through
  the record of all D₂ points and Γ₁ letters;
- the partial colour on realized records and the
  default-filled total colour on ALL record tuples
  are genuine Lean definitions.

The positive Hales–Jewett result is a source of
finite flat colour canonization, not yet a theorem
that makes these mixed records constant or supplies
a tree-compatible c-good mixed word.

**Verification:** Both #476 and #477 have passed complete Lean,
finite regressions, source graph and transitive axiom audits,
and are merged. The cumulative registered source-facing
axiom report count is 1,989; this is not a theorem-completion
percentage.
