import DualTree.ForwardQFinalTargetSkewLengths
import DualTree.ForwardQFinalSameFrontierLex
import DualTree.ForwardQFinalTargetRankBands

/-!
# Discharge the corrected target D₂-starred order from O's own skewness

This closes the geometric obstruction isolated after the exact target
Q preimage construction, for genuinely forward-corrected sources.

The selected local D₂ tail order is NOT assumed. Instead:
* at equal source T-frontier ranks the target O has equal intrinsic
  terminal ranks, ordinary lex follows the selected frontier indices,
  and O's skew II yields nondecreasing terminal word lengths. If
  their enclosing T ranks decreased, ambient complete T's skew III
  would force the reverse strict length inequality;
* across a source frontier rank jump m -> m+1, O's skew III gives
  STRICTLY increasing terminal word length, whereas the high-band
  terminal lies lex before the low-band terminal. A reversed ambient
  T-rank inequality contradicts complete-T skew III (if strict)
  or complete-T skew II (if equal).

Thus the ambient target terminal T ranks are nondecreasing with a
strict increase across the one-unit frontier band jump. The previously
certified exact compensated-T-rank criterion then yields the ACTUAL
global D₂ singleton vector-one-complete starred input condition on
the specific target-selected mixed point. Coherent relettering
therefore reconstructs the target's exact node set and complete
dependent word using a genuine corrected starred mixed-span input,
without a separate D₂ order hypothesis.

This is still a theorem for the globally FORWARD-repaired auxiliary
order and the explicitly stated complete-signature, rank-filtered
support and two-letter/span assumptions. It does not establish an
unproved equivalence with the original printed reverse-lex W_*,
nor equality of arbitrary list enumerations of the finite tree.
-/

namespace DualTree.ForwardQFinalTargetOrderFromSkew

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetRankGap
open ForwardQFinalTargetRankBands
open ForwardQFinalTargetSkewLengths
open ForwardQFinalTargetD2MixedPoint

/-- Every target terminal reconstructed at an original literal
D₂ marker is also a vertex of the genuine ambient complete T:
the assumption uses the actual FINAL rank-filtered support. -/
theorem target_terminal_mem_ambient_T
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    targetTerminalAtBullet hb g f O L hSupport i ∈ g.core.T := by
  exact ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
    g.core f (m + q) _
    (hSupport _ (target_terminal_mem_O
      hb g f O L hSupport fallback σ i))

/-- Equal selected complete-T frontier ranks force the actual
target-terminal ambient T ranks to be weakly increasing.
The crucial input is O's SKEW-II length inequality, and a
hypothetical reversed T-rank would violate T's SKEW-III. -/
theorem target_T_rank_mono_same_frontier_band
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1)
    (hfront : frontierTRank g i = frontierTRank g j) :
    terminalTRank hb g f O L hSupport i ≤
      terminalTRank hb g f O L hSupport j := by
  let ti := targetTerminalAtBullet hb g f O L hSupport i
  let tj := targetTerminalAtBullet hb g f O L hSupport j
  have hlen := target_terminal_length_le_same_frontier_rank
    hb g f O L hSupport fallback σ i j hij hfront
  change ti.length ≤ tj.length at hlen
  have hTi := target_terminal_mem_ambient_T
    hb g f O L hSupport fallback σ i
  have hTj := target_terminal_mem_ambient_T
    hb g f O L hSupport fallback σ j
  by_contra hnot
  have hrank : SkewTree.heightAt g.core.T tj <
      SkewTree.heightAt g.core.T ti := by
    change terminalTRank hb g f O L hSupport j <
      terminalTRank hb g f O L hSupport i
    omega
  have hreverse : tj.length < ti.length :=
    SkewLevelOrder.length_lt_of_height_lt
      g.core.T SkewTree.forwardAuxB
      (ForwardQFinalRetainedSkewLength.ambient_forward_skew g.core)
      g.core.hnon hTj hTi hrank
  omega

/-- A STRICT source frontier rank jump forces STRICT ambient T
rank increase between the actual target O terminals.

If the high-band target terminal had a smaller ambient T rank,
ambient skew III contradicts O's strict length separation.
If their ambient T ranks were equal, high-band-before-low-band
ordinary lex plus ambient skew II gives the opposite weak
length inequality, again contradicting O's strict separation. -/
theorem target_T_rank_strict_frontier_jump
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1)
    (hfront : frontierTRank g i < frontierTRank g j) :
    terminalTRank hb g f O L hSupport i <
      terminalTRank hb g f O L hSupport j := by
  let ti := targetTerminalAtBullet hb g f O L hSupport i
  let tj := targetTerminalAtBullet hb g f O L hSupport j
  have hiBand := frontierTRank_band g i
  have hjBand := frontierTRank_band g j
  have hi : frontierTRank g i = m := by
    rcases hiBand with h | h <;> rcases hjBand with h' | h'
    <;> omega
  have hj : frontierTRank g j = m + 1 := by
    rcases hiBand with h | h <;> rcases hjBand with h' | h'
    <;> omega
  have hlen : ti.length < tj.length :=
    target_terminal_length_lt_frontier_jump
      hb g f O L hSupport fallback σ i j hij hfront
  have hlex : FinLexLE tj ti :=
    target_terminal_lex_high_before_low
      hb g f O L hSupport fallback σ i j hi hj
  have hTi := target_terminal_mem_ambient_T
    hb g f O L hSupport fallback σ i
  have hTj := target_terminal_mem_ambient_T
    hb g f O L hSupport fallback σ j
  by_contra hnot
  have hrev :
      SkewTree.heightAt g.core.T tj ≤
        SkewTree.heightAt g.core.T ti := by
    change terminalTRank hb g f O L hSupport j ≤
      terminalTRank hb g f O L hSupport i
    omega
  rcases lt_or_eq_of_le hrev with hlt | heq
  · have hreverse : tj.length < ti.length :=
      SkewLevelOrder.length_lt_of_height_lt
        g.core.T SkewTree.forwardAuxB
        (ForwardQFinalRetainedSkewLength.ambient_forward_skew g.core)
        g.core.hnon hTj hTi hlt
    omega
  · have hreverse : tj.length ≤ ti.length :=
      ForwardQFinalSameFrontierLex.ambient_length_le_of_rank_le_and_lex
        g.core ⟨tj, hTj⟩ ⟨ti, hTi⟩
        (by exact Nat.le_of_eq heq) hlex
    omega

/-- The target terminal rank inequalities identified as the
last corrected D₂ starred-input obstruction FOLLOW from the
true source/frame and target skew hypotheses. No added global
bullet-length or terminal-rank-order premise is needed. -/
theorem target_terminal_rank_jump_order
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    TargetTerminalRankJumpOrder hb g f O L hSupport := by
  intro i j hij
  have hfront : frontierTRank g i ≤ frontierTRank g j :=
    frontierTRank_mono g i j hij
  rcases lt_or_eq_of_le hfront with hlt | heq
  · have hstrict := target_T_rank_strict_frontier_jump
      hb g f O L hSupport fallback σ i j hij hlt
    exact ⟨Nat.le_of_lt hstrict, fun _ => hstrict⟩
  · have hweak := target_T_rank_mono_same_frontier_band
      hb g f O L hSupport fallback σ i j hij heq
    exact ⟨hweak, by intro h; omega⟩

/-- Every selected target D₂ mixed-span point has the actual
corrected global starred-domain certificate, with NO new
hypothesis: it is forced by the target's own semi-complete skew
tree and the source's true two-band complete-support geometry. -/
theorem targetMixedPoint_isStarred
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    ForwardQActualStarredSpace.IsStarred g.core
      (targetMixedPoint hb g f O L hSupport fallback σ) := by
  apply (targetMixedPoint_starred_iff_target_rank_gaps
    hb g f O L hSupport fallback σ).2
  exact (target_rank_gaps_iff_terminal_rank_jump_order
    hb g f O L hSupport).2
      (target_terminal_rank_jump_order
        hb g f O L hSupport fallback σ)

/-- UNCONDITIONAL corrected starred Q reverse preimage under
the ACTUAL same-complete-signature, two-letter span and exact
rank-filtered support assumptions: a real enlarged mixed-span
point has the genuine D₂-starred certificate, the exact target
Q node SET, and the target's ENTIRE dependent rooted word.

No independent D₂ order hypothesis survives. This closes the
previously isolated local geometric admissibility obstruction,
but does not identify the printed reverse-lex W_* domain or
the arbitrary list order of the target tree. -/
theorem exists_coherent_starred_target_Q_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      w ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span ∧
      ForwardQActualStarredSpace.IsStarred g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w) ∧
      nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w) =
        O.tree.toFinset ∧
      ∀ s : BoundedNode b n,
        Sum.map id
          (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
            hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s) = O.word.word s := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  apply ForwardQFinalConditionalTargetQPreimage.exists_coherent_target_Q_preimage_of_D2_order
    hb g f fallback O cutO H hα hspan hSupport σ
  exact
    (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      g.core
        (targetMixedPoint hb g f O L hSupport fallback σ)).1
      (targetMixedPoint_isStarred
        hb g f O L hSupport fallback σ)

end DualTree.ForwardQFinalTargetOrderFromSkew
