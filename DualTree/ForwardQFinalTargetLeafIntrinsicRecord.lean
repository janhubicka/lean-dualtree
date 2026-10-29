import DualTree.ForwardQFinalIntrinsicRootedTerminal

/-!
# A local-word-free target-leaf form of the intrinsic Lemma-27 record

The preceding intrinsic record had correct OUTPUT values, but still
used a local enlarged mixed word f to select the D₂ points before
projecting them back into the target tree. This file removes that
local-word dependency from the definition itself.

For a target O with the genuine literal corrected signature and with
O.tree contained in the fixed ambient T, the verified uniqueness
of target terminals determines a leaf above EVERY original R marker.
The marker-to-bullet equivalence is fixed by the SOURCE frame alone.
At Γ₁ markers we record O's genuine root-labelled word symbol at
that leaf. There is no local Ramsey word, variable dimension,
auxiliary alphabet, fallback constant or starred-Q preimage in
this target-side observable.

We verify that this direct record agrees exactly with the previously
proved intrinsic output record whenever the target is eligible in a
genuine enlarged local mixed span. This is an interface theorem, NOT
a construction of the missing finite Ramsey witness.
-/

namespace DualTree.ForwardQFinalTargetLeafIntrinsicRecord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUniqueTargetTerminals
open ForwardQFinalCanonicalReducedRecord
open ForwardQFinalCanonicalTerminalRecord
open ForwardQFinalIntrinsicRootedTerminal

/-- The genuine target terminal chosen at bullet coordinate i,
with NO auxiliary local word or post-Ramsey support parameter. -/
noncomputable def leafAtBullet
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    {t : Node b // t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree} :=
  targetLeafForSourceMarker hb g O L hT
    ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core).symm i)

/-- The true target terminal is n-bounded by O's own certified support,
so the rooted word can be read there without a local cone address. -/
noncomputable def leafAtBulletBounded
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    BoundedNode b n :=
  ⟨(leafAtBullet hb g O L hT i).1,
    O.tree_bounded _ (leafAtBullet hb g O L hT i).2.1⟩

/-- The target-side residual invariant is a tuple of ACTUAL
target-tree leaves and, only on Γ₁, the target's root-labelled
word symbols at those leaves. This definition depends on O,
the source frame and literal-signature/ambient-support facts,
NOT on f, q, fallback or its local support certificate. -/
noncomputable def targetLeafRootedRecord
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    IntrinsicRootedRecord b n α (kind g.core) :=
  fun i =>
    ((leafAtBullet hb g O L hT i).1,
      if gamma1 i then
        some (ForwardQSimpleLetterSmooth.rootLabel O
          (leafAtBulletBounded hb g O L hT i))
      else none)

/-- The target leaf selected at the original R marker is
EXACTLY the local enlarged D₂ point's true ambient projection.
This connects the direct target record with the source-facing
support construction, but the direct record itself does not
mention that construction. -/
theorem projected_bullet_eq_leafAtBullet
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
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (projected g.core
      ⟨i.1, (canonicalReducedTargetRecord hb g f fallback O cutO H
        hSupport gamma1 i).1⟩).1 =
    (leafAtBullet hb g O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f O hSupport) i).1 := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have h := terminalReducedTargetRecord_marker_eq_targetLeaf
    hb g f fallback O cutO H hSupport gamma1 r
  rw [hi] at h
  change
    (projected g.core
      ⟨i.1, (canonicalReducedTargetRecord hb g f fallback O cutO H
        hSupport gamma1 i).1⟩).1 =
    (leafAtBullet hb g O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f O hSupport) i).1 at h
  exact h

/-- The *old* local-word-dependent intrinsic record coincides pointwise
with the new direct target-leaf record. In particular its actual values
do not depend on the choice of enlarged local Ramsey word or auxiliary
constants, once a supported target O has been fixed. -/
theorem intrinsicRootedTargetRecord_eq_targetLeafRootedRecord
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
    intrinsicRootedTargetRecord hb g f fallback O cutO H
      hSupport gamma1 =
    targetLeafRootedRecord hb g O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f O hSupport) gamma1 := by
  funext i
  let p := (canonicalReducedTargetRecord hb g f fallback O cutO H
    hSupport gamma1 i).1
  let leaf := leafAtBullet hb g O
    (ForwardQFinalFullSignature.complete_signature_implies_literal
      hb g O cutO H)
    (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
      g f O hSupport) i
  have hnode :
      (projected g.core ⟨i.1,p⟩).1 = leaf.1 :=
    projected_bullet_eq_leafAtBullet
      hb g f fallback O cutO H hSupport gamma1 i
  have hbounded :
      ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i.1 p =
        leafAtBulletBounded hb g O
          (ForwardQFinalFullSignature.complete_signature_implies_literal
            hb g O cutO H)
          (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
            g f O hSupport) i := by
    apply Subtype.ext
    exact hnode
  change
    ((projected g.core ⟨i.1,p⟩).1,
      if gamma1 i then
        some (ForwardQSimpleLetterSmooth.rootLabel O
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i.1 p))
      else none) =
    (leaf.1,
      if gamma1 i then
        some (ForwardQSimpleLetterSmooth.rootLabel O
          (leafAtBulletBounded hb g O
            (ForwardQFinalFullSignature.complete_signature_implies_literal
              hb g O cutO H)
            (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
              g f O hSupport) i))
      else none)
  rw [hnode, hbounded]

/-- A convenient fully target-facing colour-transfer interface:
the two targets need only have the SAME direct target-leaf/rooted
Γ₁ record. The record no longer mentions any chosen local word,
even though the actual c-good word and supported-span eligibility
remain assumptions of the comparison theorem. -/
theorem eligible_targets_color_eq_of_direct_targetLeaf_record
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
      targetLeafRootedRecord hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSO) gamma1 =
      targetLeafRootedRecord hb g P
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g P cutP HP)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f P hSP) gamma1) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  apply eligible_targets_color_eq_of_intrinsic_rooted_record
    hb g f fallback hα color total gamma1 hagree hsmooth hgood
      O P cutO cutP HO HP hspanO hspanP hSO hSP
  calc
    intrinsicRootedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      targetLeafRootedRecord hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSO) gamma1 :=
      intrinsicRootedTargetRecord_eq_targetLeafRootedRecord
        hb g f fallback O cutO HO hSO gamma1
    _ = targetLeafRootedRecord hb g P
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g P cutP HP)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f P hSP) gamma1 := hRecord
    _ = intrinsicRootedTargetRecord hb g f fallback P cutP HP hSP gamma1 :=
      (intrinsicRootedTargetRecord_eq_targetLeafRootedRecord
        hb g f fallback P cutP HP hSP gamma1).symm

end DualTree.ForwardQFinalTargetLeafIntrinsicRecord
