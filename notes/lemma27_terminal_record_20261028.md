# Lemma 27: canonical output-terminal residual records (28 October 2026)

**Lean verification:** PRs #454, #456, #457 and #458 are merged. The
full `lake build DualTree`, finite regression suite, source-graph audit and
1,944 registered transitive-axiom checks passed at the head of #458.
There is no end-to-end formalization of Lemma 27 or Theorem 3.

## Exact positive result

For a genuine post-Ramsey local mixed word over the enlarged alphabet
`α ⊕ Fin (m+1)`, take an eligible target `O` with the **complete**
forward-corrected signature and a true height-filtered final-support
certificate. The named `canonicalStarredTargetInput` is an actual
member of the *local* mixed span and reconstructs the target's full
tree-and-dependent-word observation through the corrected fibrewise Q.

The canonical reduced record at each genuine D₂ index stores the selected
local point `z_i` and, only at Γ₁ indices, its canonical enlarged
encoded letter. It is **not** an arbitrary `Classical.choose` of a
target Q preimage (#454). The selected points, and hence this record,
are independent of the particular local Ramsey word (including different
dimensions and auxiliary constants) when the *same target* is supported
in both final supports; they are also independent of the complete-signature
cut witness (#456).

The output-facing record of #457 is

    i ↦ (P_i(z_i), (Γ₁ i ? some encoded_letter_i : none)).

The node `P_i(z_i)` is exactly the unique **actual target terminal** above
the corresponding original source marker. The fixed projection `P_i`
is injective, so equality of these terminal records is **equivalent**
to equality of the local reduced records. Under the already checked
hypotheses—an actual enlarged local `c`-good word, a total smooth
Q-pullback agreeing on genuine starred inputs, genuine eligibility and
two source letters—equality of the terminal records implies equality
of the two target colours.

#458 further proves that the entire *output-facing terminal* record,
including the Γ₁ encoded letters, is invariant across two genuinely
enlarged local Ramsey words, across signature cut witnesses, and across
both changes simultaneously. It is therefore a stable residual
observable for later refinements, not an arbitrary refinement-dependent
choice.

## What has **not** been proved

- The residual terminal record is **not proved constant across distinct
  targets** with the same complete signature. The verified invariance
  refers to *the same target* under different local Ramsey words.
- Neither Definition 11 `c`-goodness nor Definition 21 smoothness forces
  full starred-span monochromaticity. Smoothness can erase Γ₂ marked
  **letters**, but not the Γ₂ marked **points** or Γ₁ letters.
- The printed Corollary 22 numerical statement has a Lean-checked
  smooth height-one counterexample. A corrected finite smooth mixed
  Ramsey statement with the right bounds/eligible family is still
  missing.
- Equality with the published Definition 24 canonical selector and
  reconciliation with the printed reverse-lexicographic `W_*` remain
  open. The latter is not a harmless change of index order: a
  separate typed counterexample invalidates the printed Q step.
- Lemma 27, Lemma 28, Theorem 25, Theorem 3 and Theorem 29 remain open.
  No percentage completion follows from the 1,944 axiom reports.

## Lean anchors

- `DualTree.ForwardQFinalCanonicalReducedRecord` (#454):
  `canonicalStarredTargetInput_observe_eq`,
  `eligible_targets_color_eq_of_canonical_reduced_record`.
- `DualTree.ForwardQFinalCanonicalRecordInvariance` (#456):
  `canonicalReducedTargetRecord_eq_across_local_words`,
  `canonicalReducedTargetRecord_cut_independent`.
- `DualTree.ForwardQFinalCanonicalTerminalRecord` (#457):
  `terminalReducedTargetRecord_marker_eq_targetLeaf`,
  `terminalReducedRecord_eq_iff_localRecord_eq`,
  `eligible_targets_color_eq_of_terminal_reduced_record`.
- `DualTree.ForwardQFinalCanonicalTerminalInvariance` (#458):
  `terminalReducedTargetRecord_eq_across_local_words`,
  `terminalReducedTargetRecord_cut_independent`,
  `terminalReducedTargetRecord_eq_across_words_and_cuts`.

**Next true proof obligation:** formulate and validate an applicable
Ramsey refinement theorem which controls the residual terminal/Γ₁-letter
record across *different* eligible targets, without assuming the false
strong form of Corollary 22. Then connect that invariant to the actual
Definition 24 canonical selector and run the corrected induction.
