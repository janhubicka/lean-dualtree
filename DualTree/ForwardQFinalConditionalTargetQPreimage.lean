import DualTree.ForwardQFinalTargetTreeEquality
import DualTree.ForwardQFinalCoherentWordPreimage

/-!
# Conditional exact support-and-word Q preimage in Lemma 27

The previous construction chooses the specific local D2 points
reconstructing the requested target O terminal set, and proves that
the assembled original-alphabet mixed point belongs to f.span.
The target node set is exactly the genuine corrected Q support
obtained from those D2 points.

The independent coherent enlarged-letter constructor preserves
ALL selected D2 and D1 points, remains in the alphabet-lifted local
mixed span, and its actual fibrewise Q word agrees at every ambient
homogeneous position with O under the same-complete-signature and
two-letter output-span hypotheses.

The ONLY additional assumption in this conditional preimage lemma
is that the EXACT target-selected D2 tuple satisfies the corrected
BulletLengthsOrdered (equivalently vector-one IsStarred) condition.

This yields exact Q SUPPORT-SET and dependent-WORD equality, but
does not claim equality of arbitrary tree-list enumerations or
equivalence to the printed reverse-lex starred order. Discharging
the specific global D2 order remains a genuine open obligation.
-/

namespace DualTree.ForwardQFinalConditionalTargetQPreimage

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCoherentLocalInput

/-- Changing only the ordinary coordinate words of the target
D2 mixed point to coherent enlarged auxiliary letters does not
alter its actual corrected Q support. Thus the Q support set is
already exactly the requested O.tree vertex set, without using
any global D2 order condition. -/
theorem coherent_target_Q_support_eq_output
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
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    nodes g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (coherentInput hb g f O cutO H fallback
          (ForwardQFinalTargetD2MixedPoint.targetMixedPoint
            hb g f O
              (ForwardQFinalFullSignature.complete_signature_implies_literal
                hb g O cutO H)
              hSupport fallback σ))) =
      O.tree.toFinset := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  let base := ForwardQFinalTargetD2MixedPoint.targetMixedPoint
    hb g f O L hSupport fallback σ
  have hnodes :
      nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback
          (coherentInput hb g f O cutO H fallback base)) =
        nodes g.core base := by
    classical
    rfl
  exact hnodes.trans
    (ForwardQFinalTargetTreeEquality.targetMixedPoint_Q_node_set_eq_target
      hb g f O L hSupport fallback σ)

/-- If the exact D2 points selected from the target O obey the
genuine corrected global D2 order, a REAL enlarged mixed-product
span point exists with corrected starred domain membership, exact
target Q NODE SET and exact entire dependent output WORD.

This is the precise conditional conclusion remaining after our
verified reconstruction work: no arbitrary local letter choices,
missing D2 support assumptions or fictional source-marker indices. -/
theorem exists_coherent_target_Q_preimage_of_D2_order
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
    (hOrder : ForwardQIndexedTRanks.BulletLengthsOrdered
      g.core
        (ForwardQFinalTargetD2MixedPoint.targetMixedPoint
          hb g f O
          (ForwardQFinalFullSignature.complete_signature_implies_literal
            hb g O cutO H)
          hSupport fallback σ)) :
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
  let base := ForwardQFinalTargetD2MixedPoint.targetMixedPoint
    hb g f O L hSupport fallback σ
  let w := coherentInput hb g f O cutO H fallback base
  have hspanBase : base ∈ f.span :=
    ForwardQFinalTargetD2MixedPoint.targetMixedPoint_mem_span
      hb g f O L hSupport fallback σ
  have hstarBase : ForwardQActualStarredSpace.IsStarred
      g.core base :=
    (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      g.core base).2 hOrder
  refine ⟨w,
    coherentInput_mem_mixed_span
      hb g f O cutO H fallback base hspanBase,
    coherentInput_preserves_starred
      hb g f O cutO H fallback base hstarBase,
    ?_, ?_⟩
  · exact coherent_target_Q_support_eq_output
      hb g f fallback O cutO H hSupport σ
  · intro s
    exact ForwardQFinalCoherentWordPreimage.coherentInput_matches_full_Q_word
      hb g f fallback O cutO H hα hspan base s

end DualTree.ForwardQFinalConditionalTargetQPreimage
