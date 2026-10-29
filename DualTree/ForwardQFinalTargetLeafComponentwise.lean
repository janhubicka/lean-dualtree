import DualTree.ForwardQFinalTargetLeafRecordInvariance

/-!
# Componentwise Ramsey criterion for the direct target terminal record

The record is now a genuine target-side object, independent of the
local Ramsey word, fallback and signature/support proof certificates.
This file spells out its equality in precisely the geometric and
root-labelled terms needed for the outstanding Ramsey induction.

For arbitrary eligible targets O and P, the direct records agree
if and only if:
(1) the unique target leaves above EACH original source D₂ marker agree;
(2) at Γ₁ markers only, the root-labelled target word symbols at
    those leaves agree.

No equality of target tree node sets, Γ₂ observed letters, arbitrary
word symbols, or auxiliary decoder preimages is required. Combining
this exact criterion with the verified c-good/smooth transfer gives
conditional target colour equality from these two explicit obligations.
No existence of a suitable Ramsey word is claimed here.
-/

namespace DualTree.ForwardQFinalTargetLeafComponentwise

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetLeafIntrinsicRecord
open ForwardQFinalTargetLeafRecordInvariance

/-- Equality of the direct intrinsic target record is EXACTLY
coordinatewise equality of the actual selected target terminals,
together with equality of root-labelled symbols ONLY at Γ₁ terminals. -/
theorem targetLeafRootedRecord_eq_iff_components
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (LO : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (LP : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g P)
    (hTO : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (hTP : ∀ t : Node b, t ∈ P.tree → t ∈ g.core.T)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    targetLeafRootedRecord hb g O LO hTO gamma1 =
      targetLeafRootedRecord hb g P LP hTP gamma1 ↔
    (∀ i : MixedProduct.BulletIndex (kind g.core),
      (leafAtBullet hb g O LO hTO i).1 =
        (leafAtBullet hb g P LP hTP i).1) ∧
    (∀ i : MixedProduct.BulletIndex (kind g.core),
      gamma1 i = true →
      ForwardQSimpleLetterSmooth.rootLabel O
        (leafAtBulletBounded hb g O LO hTO i) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (leafAtBulletBounded hb g P LP hTP i)) := by
  constructor
  · intro heq
    constructor
    · intro i
      have hi := congrFun heq i
      change
        ((leafAtBullet hb g O LO hTO i).1,
          if gamma1 i then
            some (ForwardQSimpleLetterSmooth.rootLabel O
              (leafAtBulletBounded hb g O LO hTO i))
          else none) =
        ((leafAtBullet hb g P LP hTP i).1,
          if gamma1 i then
            some (ForwardQSimpleLetterSmooth.rootLabel P
              (leafAtBulletBounded hb g P LP hTP i))
          else none) at hi
      exact congrArg Prod.fst hi
    · intro i hγ
      have hi := congrFun heq i
      change
        ((leafAtBullet hb g O LO hTO i).1,
          if gamma1 i then
            some (ForwardQSimpleLetterSmooth.rootLabel O
              (leafAtBulletBounded hb g O LO hTO i))
          else none) =
        ((leafAtBullet hb g P LP hTP i).1,
          if gamma1 i then
            some (ForwardQSimpleLetterSmooth.rootLabel P
              (leafAtBulletBounded hb g P LP hTP i))
          else none) at hi
      have hsecond := congrArg Prod.snd hi
      simpa only [hγ, ite_true, Option.some.injEq] using hsecond
  · rintro ⟨hterm, hletters⟩
    funext i
    change
      ((leafAtBullet hb g O LO hTO i).1,
        if gamma1 i then
          some (ForwardQSimpleLetterSmooth.rootLabel O
            (leafAtBulletBounded hb g O LO hTO i))
        else none) =
      ((leafAtBullet hb g P LP hTP i).1,
        if gamma1 i then
          some (ForwardQSimpleLetterSmooth.rootLabel P
            (leafAtBulletBounded hb g P LP hTP i))
        else none)
    apply Prod.ext
    · exact hterm i
    · cases hγ : gamma1 i with
      | false => simp [hγ]
      | true =>
        simpa only [hγ, ite_true, Option.some.injEq]
          using hletters i hγ

/-- The corrected target-colour comparison from the TWO explicit
remaining observables: agreement of actual target terminal nodes at
ALL D₂ markers, and rooted word symbols at Γ₁ markers ONLY.
The proofs of the signature and ambient-T inclusion used to express
this pairwise criterion need not be the ones produced by the
local Ramsey target-support certificates. -/
theorem eligible_targets_color_eq_of_leaf_and_gamma1_symbols
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
    (LO : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (LP : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g P)
    (hTO : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (hTP : ∀ t : Node b, t ∈ P.tree → t ∈ g.core.T)
    (hterm : ∀ i : MixedProduct.BulletIndex (kind g.core),
      (leafAtBullet hb g O LO hTO i).1 =
        (leafAtBullet hb g P LP hTP i).1)
    (hletters : ∀ i : MixedProduct.BulletIndex (kind g.core),
      gamma1 i = true →
      ForwardQSimpleLetterSmooth.rootLabel O
        (leafAtBulletBounded hb g O LO hTO i) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (leafAtBulletBounded hb g P LP hTP i)) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  have hrec : targetLeafRootedRecord hb g O LO hTO gamma1 =
      targetLeafRootedRecord hb g P LP hTP gamma1 :=
    (targetLeafRootedRecord_eq_iff_components
      hb g O P LO LP hTO hTP gamma1).2 ⟨hterm,hletters⟩
  apply eligible_targets_color_eq_of_direct_targetLeaf_record
    hb g f fallback hα color total gamma1 hagree hsmooth hgood
      O P cutO cutP HO HP hspanO hspanP hSO hSP
  calc
    targetLeafRootedRecord hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSO) gamma1 =
      targetLeafRootedRecord hb g O LO hTO gamma1 :=
      targetLeafRootedRecord_certificate_independent hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO) LO
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSO) hTO gamma1
    _ = targetLeafRootedRecord hb g P LP hTP gamma1 := hrec
    _ = targetLeafRootedRecord hb g P
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g P cutP HP)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f P hSP) gamma1 :=
      targetLeafRootedRecord_certificate_independent hb g P LP
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g P cutP HP) hTP
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f P hSP) gamma1

end DualTree.ForwardQFinalTargetLeafComponentwise
