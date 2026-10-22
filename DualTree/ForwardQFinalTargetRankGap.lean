import DualTree.ForwardQFinalConditionalTargetQPreimage
import DualTree.ForwardQIndexedTRanks
import DualTree.ForwardQFinalTargetD2MixedPoint
import DualTree.ForwardQFinalUniqueTargetTerminals

/-!
# Lemma 27: raw target preimage and exact D₂ rank-gap obstruction

The exact target Q support and its entire dependent output word can be
reconstructed by a genuine coherent mixed-span input WITHOUT proving the
corrected vector-one D₂ starred-domain condition. We isolate that
unconditional raw preimage, rather than silently identifying it with
a starred Q-input.

For the PARTICULAR target-selected D₂ points, the remaining corrected
starred-domain condition is equivalent to inequalities between their
ambient T ranks after compensation by the source frontier T ranks.
These inequalities depend on the target terminals and the local
variable supports, not on the arbitrary fallback letter or the
coherent input's root-letter assignment.

This is a reduction of the outstanding Lemma 27 problem, NOT a
derivation of the rank inequalities from equal complete signatures.
In particular no equivalence with the printed reverse-lex W_* is
asserted.
-/

namespace DualTree.ForwardQFinalTargetRankGap

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCoherentLocalInput
open ForwardQFinalUniqueTargetTerminals
open ForwardQFinalTargetD2MixedPoint

/-- The unique target O terminal corresponding to the original
literal R marker at this genuine sorted D₂ bullet index. This
definition is independent of the fallback letter and of any
word/root-value assignment used when constructing the Q input. -/
noncomputable def targetTerminalAtBullet
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
    (i : MixedProduct.BulletIndex (kind g.core)) : Node b :=
  (targetLeafForSourceMarker hb g O L
    (ForwardQFinalTargetD2Point.targetTree_subset_complete_of_final_support
      g f O hSupport)
    ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
      g.core).symm i)).1

/-- The actual target mixed-point projection is exactly this target
terminal at each D₂ index. The equality does not depend on either
the output alphabet fallback or the assignment σ. -/
theorem targetMixedPoint_projection_eq_targetTerminal
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
    (markedProjection g.core
      (targetMixedPoint hb g f O L hSupport fallback σ) i).1 =
      targetTerminalAtBullet hb g f O L hSupport i := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
    g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  change (markedProjection g.core
      (targetMixedPoint hb g f O L hSupport fallback σ) i).1 =
    (targetLeafForSourceMarker hb g O L
      (ForwardQFinalTargetD2Point.targetTree_subset_complete_of_final_support
        g f O hSupport) r).1
  rw [← hi]
  exact targetMixedPoint_markedProjection_eq_targetLeaf
    hb g f O L hSupport fallback σ r

/-- For two D₂ indices, comparing the LENGTHS of the selected local
tails is EXACTLY comparing their ambient T terminal ranks after
compensating for the two possibly unequal frontier ranks. The
compensation is essential: frontier T ranks may differ by one. -/
theorem target_tail_length_le_iff_compensated_T_ranks
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
    (i j : MixedProduct.BulletIndex (kind g.core)) :
    (targetBulletPoint hb g f O L hSupport i).1.length ≤
        (targetBulletPoint hb g f O L hSupport j).1.length ↔
      SkewTree.heightAt g.core.T
        (targetTerminalAtBullet hb g f O L hSupport i) +
          SkewTree.heightAt g.core.T
            (ForwardOrderedProjections.frontierAt
              g.core.T g.core.cut j.1).1 ≤
      SkewTree.heightAt g.core.T
        (targetTerminalAtBullet hb g f O L hSupport j) +
          SkewTree.heightAt g.core.T
            (ForwardOrderedProjections.frontierAt
              g.core.T g.core.cut i.1).1 := by
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hi := ForwardQIndexedTRanks.marked_T_rank_formula
    g.core x i
  have hj := ForwardQIndexedTRanks.marked_T_rank_formula
    g.core x j
  have hprojI := targetMixedPoint_projection_eq_targetTerminal
    hb g f O L hSupport fallback σ i
  have hprojJ := targetMixedPoint_projection_eq_targetTerminal
    hb g f O L hSupport fallback σ j
  rw [hprojI] at hi
  rw [hprojJ] at hj
  change SkewTree.heightAt g.core.T
        (targetTerminalAtBullet hb g f O L hSupport i) =
      SkewTree.heightAt g.core.T
        (ForwardOrderedProjections.frontierAt
          g.core.T g.core.cut i.1).1 +
      (targetBulletPoint hb g f O L hSupport i).1.length at hi
  change SkewTree.heightAt g.core.T
        (targetTerminalAtBullet hb g f O L hSupport j) =
      SkewTree.heightAt g.core.T
        (ForwardOrderedProjections.frontierAt
          g.core.T g.core.cut j.1).1 +
      (targetBulletPoint hb g f O L hSupport j).1.length at hj
  constructor <;> intro h <;> omega

/-- Exact output-side obstruction to the corrected D₂ vector-one
ordering: the target T ranks must increase sufficiently to offset
the possible increase in source frontier T rank. Unlike the mixed
input's IsStarred, this condition mentions no fallback or σ. -/
def TargetRankGapsOrdered
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
        g.core f (m + q)) : Prop :=
  ∀ i j : MixedProduct.BulletIndex (kind g.core), i.1 < j.1 →
    SkewTree.heightAt g.core.T
      (targetTerminalAtBullet hb g f O L hSupport i) +
        SkewTree.heightAt g.core.T
          (ForwardOrderedProjections.frontierAt
            g.core.T g.core.cut j.1).1 ≤
    SkewTree.heightAt g.core.T
      (targetTerminalAtBullet hb g f O L hSupport j) +
        SkewTree.heightAt g.core.T
          (ForwardOrderedProjections.frontierAt
            g.core.T g.core.cut i.1).1

/-- The EXACT global D₂-starred hypothesis on the selected target
mixed point is equivalent to the compensated T-rank inequalities
of the target terminals, for any chosen fallback and σ. -/
theorem targetMixedPoint_order_iff_target_rank_gaps
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
    ForwardQIndexedTRanks.BulletLengthsOrdered g.core
      (targetMixedPoint hb g f O L hSupport fallback σ) ↔
    TargetRankGapsOrdered hb g f O L hSupport := by
  constructor
  · intro horder i j hij
    exact (target_tail_length_le_iff_compensated_T_ranks
      hb g f O L hSupport fallback σ i j).1 (horder i j hij)
  · intro hgap i j hij
    exact (target_tail_length_le_iff_compensated_T_ranks
      hb g f O L hSupport fallback σ i j).2 (hgap i j hij)

/-- In particular, the legal corrected starred-domain predicate for
the concrete target mixed point is fully characterized by those
output-side inequalities, independently of its ordinary word data. -/
theorem targetMixedPoint_starred_iff_target_rank_gaps
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
      (targetMixedPoint hb g f O L hSupport fallback σ) ↔
    TargetRankGapsOrdered hb g f O L hSupport := by
  exact (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
    g.core (targetMixedPoint hb g f O L hSupport fallback σ)).trans
    (targetMixedPoint_order_iff_target_rank_gaps
      hb g f O L hSupport fallback σ)

/-- UNCONDITIONAL raw preimage: there is an actual coherent enlarged
mixed-span point with the exact requested Q TREE NODE SET and WHOLE
dependent Q WORD. The only thing NOT provided is membership in the
corrected starred D₂ input domain. This is a strictly stronger raw
reconstruction statement than the conditional starred preimage. -/
theorem exists_coherent_raw_target_Q_preimage
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
  let base := targetMixedPoint hb g f O L hSupport fallback σ
  let w := coherentInput hb g f O cutO H fallback base
  have hbase : base ∈ f.span :=
    targetMixedPoint_mem_span hb g f O L hSupport fallback σ
  refine ⟨w, ?_, ?_, ?_⟩
  · exact coherentInput_mem_mixed_span
      hb g f O cutO H fallback base hbase
  · exact ForwardQFinalConditionalTargetQPreimage.coherent_target_Q_support_eq_output
      hb g f fallback O cutO H hSupport σ
  · intro s
    exact ForwardQFinalCoherentWordPreimage.coherentInput_matches_full_Q_word
      hb g f fallback O cutO H hα hspan base s

/-- Strengthen raw reconstruction to an actual starred mixed input
whenever the TARGET terminal ranks satisfy the precise compensated
rank-order condition. This is a target-only hypothesis: it cannot
silently be inferred from the source's printed W_* convention. -/
theorem exists_coherent_starred_target_Q_preimage_of_rank_gaps
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
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (hGap : TargetRankGapsOrdered hb g f O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H) hSupport) :
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
  apply ForwardQFinalConditionalTargetQPreimage.exists_coherent_target_Q_preimage_of_D2_order
    hb g f fallback O cutO H hα hspan hSupport σ
  exact (targetMixedPoint_order_iff_target_rank_gaps
    hb g f O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H)
      hSupport fallback σ).2 hGap

end DualTree.ForwardQFinalTargetRankGap
