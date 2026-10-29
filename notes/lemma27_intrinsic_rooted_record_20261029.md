# Lemma 27: rooted Γ₁ records and the remaining Ramsey problem
**29 October 2026 — verified through merged #466 (1,959 source-facing axiom reports).**

## The precise new advance

The genuine enlarged Q alphabet has the form `α ⊕ Fin(m+1)`. Its
auxiliary decoder maps many labels to the same visible source root when
the target set of visible roots is smaller than `m+1`. In particular
the decoder is only surjective, and assuming injectivity would be a
mathematical error.

The existing target encoder
`ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol`
is defined by `Classical.choose` of a *full decoder fibre*. The new
`ForwardQFinalEncoderExtensional` module (#464) proves that the defining
fibre predicate depends only on the **actual root-labelled output
symbol**, via the root-preserving source/output variable equivalence.
For the same frontier and projected coordinate, equal root-labelled
symbols give logically equivalent predicates. `propext` and proof
irrelevance then yield equality of the existing chosen auxiliary
letters, despite noninjectivity of the raw decoder.

The proof never replaces the existing encoder with an unrelated
selection that could change which colours c-goodness distinguishes.

## Colour factorization, with progressively weaker geometry premises

1. **#461, Γ₁ empty.** For eligible targets with equal finite node sets,
   all selected D₂ terminal positions coincide. If Γ₁ is empty there
   are no residual letters, so the genuine smooth/c-good pullback
   gives equal colours.
2. **#465, arbitrary Γ₁/Γ₂.** The same node-set hypothesis, plus
   equality of rooted output symbols at Γ₁-marked terminal positions
   only, implies equality of the actual chosen enlarged letters.
   No Γ₂ letters or entire word equality are needed.
3. **#466, arbitrary target trees.** Define
   `ForwardQFinalIntrinsicRootedTerminal.intrinsicRootedTargetRecord`
   at each genuine D₂ index `i` by

       (actual target terminal t_i,
        if Γ₁ i then some(rootLabel O at t_i) else none).

   The first component is a real homogeneous-tree node and the
   optional second component uses α or an actual bounded variable
   root—not a dependent subtype proof, a local D₂ address, or an
   auxiliary Fin(m+1) label.

   Kernel-checked `intrinsicRootedRecord_eq_implies_terminalReducedRecord_eq`
   shows that equality of these records for **any two eligible
   targets** implies equality of their previous concrete enlarged
   target-terminal records. Equality of terminal components recovers
   local D₂ addresses by true cone-projection injectivity. Equality
   of Γ₁ rooted symbols then recovers the actual chosen enlarged
   letters by #464.

   The theorem
   `eligible_targets_color_eq_of_intrinsic_rooted_record`
   transfers this to equality of target colours using exactly the
   existing smoothness and Definition-11 c-goodness conditions.

The new result is **conditional factorization**, not a proof of
monochromaticity. In particular it does not assume that different
target trees coincide: they may have different node sets so long as
the selected intrinsic record is equal.

## Remaining obligations — not discharged

- **Existence of the local Ramsey word.** All target colour-transfer
  statements assume an actual enlarged local mixed variable word
  `f` for which `MixedProduct.Good total f` holds and a genuine
  total smooth Q-pullback. No theorem here constructs that word at
  the necessary quantitative parameters or forces the intrinsic
  target records to agree across a Ramsey refinement.
- **Direct target-side intrinsic definition.** #466's record has
  intrinsic *values* but is still presented using a locally supported
  word `f` and a chosen complete-signature witness to locate the
  terminal. Previous Lean results show the local D₂ points and
  auxiliary target record are stable across suitable refinements;
  a separate theorem identifying the new rooted record with a
  target-leaf definition independent of `f` would simplify the
  final induction further.
- **Printed Definition 24 selector**: its canonical root-and-successor
  laws on corrected Q images remain a conditional interface.
- **Source corrections:** reverse-lexicographic printed `W_*`,
  unary-alphabet evaluated-span collapse, false printed
  Corollary-22 threshold (global numerical wrapper not yet
  assembled as a Lean theorem), and later signature-transport
  details must be handled explicitly.
- **Unproved complete results:** Theorem 13's full gluing,
  Lemmas 27–28 and Theorems 25, 3, 29.

## Verification anchors

- #464: `ForwardQFinalEncoderExtensional.encodeProjectedOutputSymbol_eq_of_rootLabel`
  and its dependent-symbol erasure and choice-predicate lemmas.
- #465: `ForwardQFinalSameTreeGamma1.terminalReducedTargetRecord_eq_of_same_tree_gamma1_symbols`
  and `eligible_targets_color_eq_of_same_tree_gamma1_symbols`.
- #466: `ForwardQFinalIntrinsicRootedTerminal.intrinsicRootedTargetRecord`,
  `intrinsicRootedRecord_eq_implies_terminalReducedRecord_eq`, and
  `eligible_targets_color_eq_of_intrinsic_rooted_record`.

The complete Lean umbrella, finite regressions, source gate and
`#print axioms` audit passed on each merged proof PR. The cumulative
1,959 audited endpoints are NOT a theorem-completion percentage.

**Most useful next mathematical target:** formulate and prove a
corrected finite smooth mixed Ramsey refinement that canonizes the
intrinsic rooted target-terminal record on the eligible target class
(without assuming the false full starred-span monochromaticity
conclusion), then discharge Definition 24's genuine selector laws and
run the Lemma 27/28 induction.
