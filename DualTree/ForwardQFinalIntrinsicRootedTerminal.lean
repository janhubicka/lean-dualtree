import DualTree.ForwardQFinalSameTreeGamma1

/-!
# Intrinsic rooted terminal observation controlling corrected target colours

The enlarged auxiliary decoder is not injective; nevertheless the ACTUAL
chosen encoder was shown extensional in the rooted output symbol (#464).
Thus one can formulate the remaining colour invariant without mentioning
the arbitrary auxiliary alphabet or a particular Q-input representation.

At every source D₂ marker, retain:
* the actual target terminal (a Node b);
* at Γ₁ indices only, the target's rooted output symbol THERE,
  with original constants or actual bounded variable roots.

The target may vary freely: no equality of its complete tree sets
or of its raw input words is assumed. Equality of these reduced
intrinsic records implies equality of the concrete enlarged Q
reduced records via (1) cone-projection injectivity and (2) the
new choice-extensionality lemma. The genuine Definition 11/21
target-colour comparison then applies.

The missing finite smooth Ramsey theorem must eventually produce
a refinement where this intrinsic record is controlled; this module
does not assume any false starred-span monochromaticity.
-/

namespace DualTree.ForwardQFinalIntrinsicRootedTerminal

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCanonicalReducedRecord
open ForwardQFinalCanonicalTerminalRecord
open ForwardQFinalEncoderExtensional

/-- The source-independent *type* of the remaining corrected
Lemma-27 target observable: a true target terminal at EVERY D₂ index,
and a rooted target word symbol only at Γ₁ indices. Unlike the
previous auxiliary encoded letters, it lives entirely on actual
bounded nodes and original rooted output symbols. -/
abbrev IntrinsicRootedRecord
    (b n : Nat) (α : Type*)
    {d : Nat} (kind : Fin d → MixedProduct.CoordKind) :=
  MixedProduct.BulletIndex kind →
    (Node b × Option (Sum α (BoundedNode b n)))

/-- A genuine eligible target's intrinsic reduced record, built by
projecting its selected true local D₂ variable points. Its Γ₁
component uses the actual rooted target symbol, not an arbitrary
preimage letter of the many-to-one Q decoder. -/
noncomputable def intrinsicRootedTargetRecord
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    IntrinsicRootedRecord b n α (kind g.core) :=
  fun i =>
    let r := canonicalReducedTargetRecord hb g f fallback O cutO H
      hSupport gamma1 i
    ((projected g.core ⟨i.1,r.1⟩).1,
      if gamma1 i then
        some (ForwardQSimpleLetterSmooth.rootLabel O
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i.1 r.1))
      else none)

/-- Equality of the rooted-symbol records implies equality of the
ACTUAL enlarged auxiliary terminal records for any pair of eligible
targets, even if their target TREE SETS differ.

The point projection determines the local D₂ address, and at Γ₁
the target-rooted-symbol equality determines the existing chosen
auxiliary letter by the verified choice-extensionality theorem. -/
theorem intrinsicRootedRecord_eq_implies_terminalReducedRecord_eq
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
    (hRecord :
      intrinsicRootedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      intrinsicRootedTargetRecord hb g f fallback P cutP HP hSP gamma1) :
    terminalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      terminalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1 := by
  funext i
  let rO := canonicalReducedTargetRecord
    hb g f fallback O cutO HO hSO gamma1 i
  let rP := canonicalReducedTargetRecord
    hb g f fallback P cutP HP hSP gamma1 i
  have hRecordI := congrFun hRecord i
  change ((projected g.core ⟨i.1,rO.1⟩).1,
        if gamma1 i then some (ForwardQSimpleLetterSmooth.rootLabel O
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i.1 rO.1)) else none) =
      ((projected g.core ⟨i.1,rP.1⟩).1,
        if gamma1 i then some (ForwardQSimpleLetterSmooth.rootLabel P
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i.1 rP.1)) else none) at hRecordI
  have hterm :
      (projected g.core ⟨i.1,rO.1⟩).1 =
        (projected g.core ⟨i.1,rP.1⟩).1 :=
    congrArg Prod.fst hRecordI
  have hlocal : rO.1 = rP.1 := by
    apply ForwardQFinalRefinementRoots.projectLocal_injective g.core i.1
    apply Subtype.ext
    exact hterm
  change ((projected g.core ⟨i.1,rO.1⟩).1,
        if gamma1 i then
          some (ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
            hb g O cutO HO fallback i.1 rO.1) else none) =
      ((projected g.core ⟨i.1,rP.1⟩).1,
        if gamma1 i then
          some (ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
            hb g P cutP HP fallback i.1 rP.1) else none)
  apply Prod.ext
  · exact hterm
  · cases hg : gamma1 i with
    | false => simp [hg]
    | true =>
      have hletters := congrArg Prod.snd hRecordI
      simp only [hg, ite_true, Option.some.injEq] at hletters
      rw [← hlocal] at hletters
      have henc := encodeProjectedOutputSymbol_eq_of_rootLabel
        hb g O P cutO cutP HO HP fallback i.1 rO.1 hletters
      simp only [hg, ite_true, Option.some.injEq]
      rw [← hlocal]
      exact henc

/-- Source-faithful corrected Lemma-27 conditional target factorization
through the intrinsic rooted terminal record. The target trees themselves
need NOT agree: equality of their D₂ terminal / Γ₁ rooted-symbol
records is the precise residual observable for future Ramsey arguments.
The actual local c-good word and smooth Q pullback remain explicit
hypotheses, NOT conclusions. -/
theorem eligible_targets_color_eq_of_intrinsic_rooted_record
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
    (hRecord :
      intrinsicRootedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      intrinsicRootedTargetRecord hb g f fallback P cutP HP hSP gamma1) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  apply eligible_targets_color_eq_of_terminal_reduced_record
    hb g f fallback hα color total gamma1 hagree hsmooth hgood
      O P cutO cutP HO HP hspanO hspanP hSO hSP
  exact intrinsicRootedRecord_eq_implies_terminalReducedRecord_eq
    hb g f fallback O P cutO cutP HO HP hSO hSP gamma1 hRecord

end DualTree.ForwardQFinalIntrinsicRootedTerminal
