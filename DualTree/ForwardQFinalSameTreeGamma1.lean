import DualTree.ForwardQFinalEncoderExtensional

/-!
# A genuinely cross-target Γ₁/Γ₂ factorization on fixed target trees

The completed source-side encoder extensionality theorem says that
two output words inducing the SAME rooted symbol at one fixed
projected coordinate receive identical concrete enlarged letters.
This does NOT use injectivity of the auxiliary Q decoder.

Here two supported corrected-signature target trees may have different
rooted words but share the same finite tree NODE SET. The verified
unique-terminal and cone-projection results force equality of their
selected D₂ local addresses. Equality of the actual rooted output
symbols ONLY at the marked Γ₁ terminals therefore gives equality of
the remaining chosen enlarged Γ₁ letters. Their reduced terminal
records coincide, and the genuine c-good/smooth target transfer gives
the same target colour.

Neither full target-word equality nor Γ₂ letter equality is assumed.
No local c-good Ramsey word is constructed, and this does not force
different target trees to become equal.
-/

namespace DualTree.ForwardQFinalSameTreeGamma1

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCanonicalReducedRecord
open ForwardQFinalCanonicalTerminalRecord
open ForwardQFinalEncoderExtensional

/-- Two supported targets with the same node set have the same entire
reduced terminal record when their ROOTED symbols agree only at
Γ₁-marked projected terminals. Γ₂ letters and every unmarked word
position are deliberately absent from the hypothesis. -/
theorem terminalReducedTargetRecord_eq_of_same_tree_gamma1_symbols
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g P cutP)
    (hSO : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hSP : ∀ t : Node b, t ∈ P.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (hTree : O.tree.toFinset = P.tree.toFinset)
    (hGamma1 : ∀ i : MixedProduct.BulletIndex (kind g.core),
      gamma1 i = true →
      ForwardQSimpleLetterSmooth.rootLabel O
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i.1
          (canonicalReducedTargetRecord hb g f fallback
            O cutO HO hSO gamma1 i).1) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i.1
          (canonicalReducedTargetRecord hb g f fallback
            O cutO HO hSO gamma1 i).1)) :
    terminalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      terminalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1 := by
  funext i
  let rO := canonicalReducedTargetRecord
    hb g f fallback O cutO HO hSO gamma1 i
  let rP := canonicalReducedTargetRecord
    hb g f fallback P cutP HP hSP gamma1 i
  have hfirst :=
    ForwardQFinalSameTreeGamma2.terminalReducedTargetRecord_fst_eq_of_same_tree
      hb g f fallback O P cutO cutP HO HP hSO hSP gamma1 hTree i
  change (projected g.core ⟨i.1,rO.1⟩).1 =
    (projected g.core ⟨i.1,rP.1⟩).1 at hfirst
  have hlocal : rO.1 = rP.1 := by
    apply ForwardQFinalRefinementRoots.projectLocal_injective g.core i.1
    apply Subtype.ext
    exact hfirst
  change ((projected g.core ⟨i.1,rO.1⟩).1,
      if gamma1 i then
        some (ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
          hb g O cutO HO fallback i.1 rO.1) else none) =
    ((projected g.core ⟨i.1,rP.1⟩).1,
      if gamma1 i then
        some (ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
          hb g P cutP HP fallback i.1 rP.1) else none)
  apply Prod.ext
  · exact hfirst
  · cases hg : gamma1 i with
    | false => simp [hg]
    | true =>
      have hlabels :
          ForwardQSimpleLetterSmooth.rootLabel O
            (ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i.1 rO.1) =
          ForwardQSimpleLetterSmooth.rootLabel P
            (ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i.1 rO.1) :=
        hGamma1 i hg
      have he :=
        encodeProjectedOutputSymbol_eq_of_rootLabel
          hb g O P cutO cutP HO HP fallback i.1 rO.1 hlabels
      simp only [hg, ite_true, Option.some.injEq]
      rw [← hlocal]
      exact he

/-- Under the genuine Definition-11 c-good and Definition-21 smooth
hypotheses, TWO eligible same-tree targets have equal colours when
their actual rooted output symbols agree at Γ₁-marked terminals.
This is the all-Γ₂ theorem strengthened to an ARBITRARY Γ₁/Γ₂ split.
Nothing assumes or concludes general starred-span monochromaticity. -/
theorem eligible_targets_color_eq_of_same_tree_gamma1_symbols
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : ForwardQFinalTargetObservation.Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput g.core → γ)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 = color (ForwardQFinalTargetObservation.observe
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord hb g fallback w)))
    (hsmooth : ∀ x y : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      MixedProduct.SmoothRelated gamma1 x y → total x = total y)
    (hgood : MixedProduct.Good total f)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g P cutP)
    (hspanO : O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hspanP : P.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSO : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hSP : ∀ t : Node b, t ∈ P.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hTree : O.tree.toFinset = P.tree.toFinset)
    (hGamma1 : ∀ i : MixedProduct.BulletIndex (kind g.core),
      gamma1 i = true →
      ForwardQSimpleLetterSmooth.rootLabel O
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i.1
          (canonicalReducedTargetRecord hb g f fallback
            O cutO HO hSO gamma1 i).1) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i.1
          (canonicalReducedTargetRecord hb g f fallback
            O cutO HO hSO gamma1 i).1)) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  apply eligible_targets_color_eq_of_terminal_reduced_record
    hb g f fallback hα color total gamma1 hagree hsmooth hgood
      O P cutO cutP HO HP hspanO hspanP hSO hSP
  exact terminalReducedTargetRecord_eq_of_same_tree_gamma1_symbols
    hb g f fallback O P cutO cutP HO HP hSO hSP gamma1 hTree hGamma1

end DualTree.ForwardQFinalSameTreeGamma1
