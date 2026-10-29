# Lemma 27: the genuinely direct target-leaf / Γ₁ rooted record

**29 October 2026.** Verification milestones are PRs #468–470.
The full theorem is **not** proved. The three new modules are deliberately
an interface to the outstanding corrected finite smooth Ramsey step.

## A record defined on target O, not on a local Ramsey word

Fix a corrected source frame `g`, an eligible target starred object `O`
with the corrected **literal** source signature, and a certificate that
`O.tree` lies inside the enclosing complete support `T`. The existing
uniqueness theorem
`ForwardQFinalUniqueTargetTerminals.unique_target_terminal_for_source_marker`
gives exactly one terminal `t_i(O)` of `O.tree` above the original
source marker associated with each `D₂` coordinate `i`.

The direct record
`ForwardQFinalTargetLeafIntrinsicRecord.targetLeafRootedRecord`
stores, at every `D₂` index,

    (t_i(O), if gamma1 i then some(rootLabel O at t_i(O)) else none).

The second entry uses the real `α` constant or the variable's actual
bounded root, not its dependent subtype proof and not any auxiliary
`Fin(m+1)` label. The leaf is bounded using `O.tree_bounded`, not
a fictitious local variable root.

The **definition does not contain** the post-Ramsey local mixed
word `f`, its dimension `q`, its fallback original-alphabet constant,
its rank-filtered final support or a choice of a starred Q preimage.

### Validated bridge back to the genuine enlarged local construction

PR #468 verifies two relevant facts:

1. The projected **actual** selected local `D₂` point is exactly the
   unique target terminal above the same original source marker.
2. On every genuinely supported eligible target, the older
   `intrinsicRootedTargetRecord` from #466 agrees **pointwise** with
   `targetLeafRootedRecord`.

Thus the known conditional Definition-11 c-good and Definition-21
smooth Q-pullback comparison may now be phrased as:
**equality of the direct target records implies equality of the
two eligible target colours**.

This statement still explicitly assumes a genuine local c-good
mixed variable word, total smooth pullback, two original alphabet
letters and the proper complete-signature/final-support/span
eligibility certificates. It is not full starred monochromaticity.

### Witness independence

PR #469 proves the direct record does not depend on which proofs
of the literal signature and ambient-T inclusion are passed.
Consequently the older output-facing intrinsic record is invariant
for the SAME target O even if two supported enlarged local words
have different dimensions and fallback constants, as well as
different complete-signature cuts and support certificates.

This removes a bookkeeping dependency; it does not canonize
the record of two different targets.

### The exact componentwise Ramsey target

PR #470 packages equality of the direct records into the two
**necessary and sufficient** conditions:

* the genuine selected target terminal nodes coincide at ALL
  source D₂ markers;
* the true rooted word symbols at those terminals coincide
  **only** for Γ₁ markers.

In particular no hypothesis equates entire target tree node sets,
whole rooted words, Γ₂ marked letters or raw auxiliary encoder
preimages. The corresponding conditional target-colour theorem
permits independent literal-signature and T-containment proofs
for the two targets: PR #469 guarantees these proofs cannot
affect the record.

## Outstanding mathematical obligations

1. Find and prove an actually valid finite smooth mixed Ramsey
   theorem which supplies the required local `c`-good word and
   controls these two remaining componentwise observables across
   the eligible corrected target class. The printed Corollary 22
   bound cannot be used as stated; it has a genuine height-one
   smooth-colouring obstruction in the Lean audit (the full
   numerical MTHJ/CT wrapper remains to be assembled as one theorem).
2. Identify the published Definition 24 canonical selector with
   the verified corrected source-relative selector, at least
   on genuine Q outputs. Its root/successor laws are currently
   a conditional interface.
3. Reconcile or explicitly replace the printed reverse-lexicographic
   starred Q domain with the forward-corrected construction, and
   complete Lemma 27's induction, Lemma 28's signature transport,
   Theorems 25/3 and the product theorem.

## Exact Lean anchors

- `ForwardQFinalTargetLeafIntrinsicRecord.leafAtBullet`
- `ForwardQFinalTargetLeafIntrinsicRecord.leafAtBulletBounded`
- `ForwardQFinalTargetLeafIntrinsicRecord.targetLeafRootedRecord`
- `ForwardQFinalTargetLeafIntrinsicRecord.projected_bullet_eq_leafAtBullet`
- `ForwardQFinalTargetLeafIntrinsicRecord.intrinsicRootedTargetRecord_eq_targetLeafRootedRecord`
- `ForwardQFinalTargetLeafIntrinsicRecord.eligible_targets_color_eq_of_direct_targetLeaf_record`
- `ForwardQFinalTargetLeafRecordInvariance.targetLeafRootedRecord_certificate_independent`
- `ForwardQFinalTargetLeafRecordInvariance.intrinsicRootedTargetRecord_eq_across_words_fallbacks_and_cuts`
- `ForwardQFinalTargetLeafComponentwise.targetLeafRootedRecord_eq_iff_components`
- `ForwardQFinalTargetLeafComponentwise.eligible_targets_color_eq_of_leaf_and_gamma1_symbols`

The complete umbrella, finite regressions, source gate and registered
transitive axiom checks are required before each PR is considered
verified. **1,969** is the expected source-facing endpoint count
through #470, not a theorem-completion percentage.
