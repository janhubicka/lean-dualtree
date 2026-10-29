import DualTree.ForwardQFinalCanonicalTerminalInvariance

/-!
# Same-tree target colour transfer in the all-Γ₂ case

The verified output-terminal record is independent of the *local Ramsey
word* for a fixed target. Here we compare TWO POSSIBLY DIFFERENT target
starred words. If they have exactly the same finite tree, then the unique
target terminal above each original literal source marker is the same.

For the special partition Γ₁ = ∅, the residual canonical record retains
only these target terminals, with no marked letters. Thus it is equal
for any two eligible targets with the same tree, and smooth c-good
colour transfer gives equal target colours.

This is an actual cross-target conclusion, but it does NOT say the
target trees become equal on the Ramsey refinement. In the general
Γ₁/Γ₂ split the Γ₁ observed letters remain an additional obstruction.
-/

namespace DualTree.ForwardQFinalSameTreeGamma2

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUniqueTargetTerminals
open ForwardQFinalCanonicalTerminalRecord

/-- The uniquely selected terminal above an original literal source
marker is an intrinsic property of the TARGET TREE. It is independent
of the word labels, the signature proof and the support witness,
provided the two targets have equal finite node sets. -/
theorem targetLeaf_eq_of_same_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (LO : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature hb g O)
    (LP : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature hb g P)
    (hTO : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (hTP : ∀ t : Node b, t ∈ P.tree → t ∈ g.core.T)
    (hTree : O.tree.toFinset = P.tree.toFinset)
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    (targetLeafForSourceMarker hb g O LO hTO r).1 =
      (targetLeafForSourceMarker hb g P LP hTP r).1 := by
  classical
  let leafO := targetLeafForSourceMarker hb g O LO hTO r
  let leafP := targetLeafForSourceMarker hb g P LP hTP r
  have hMemP : leafO.1 ∈ P.tree := by
    apply List.mem_toFinset.mp
    rw [← hTree]
    exact List.mem_toFinset.mpr leafO.2.1
  have hNotP : leafO.1 ∉ SkewTree.interior P.tree := by
    intro hInteriorP
    have hSource :=
      (ForwardQFinalLiteralSignatureTree.literal_signature_trees_force_same_interior
        hb g P LP leafO.1).1 hInteriorP
    exact leafO.2.2
      ((ForwardQFinalLiteralSignatureTree.literal_signature_trees_force_same_interior
        hb g O LO leafO.1).2 hSource)
  let leafOasP :
      {t : Node b // t ∈ P.tree ∧ t ∉ SkewTree.interior P.tree} :=
    ⟨leafO.1, hMemP, hNotP⟩
  have hPrefix : IsPrefix r.1 leafOasP.1 :=
    targetLeafForSourceMarker_prefix hb g O LO hTO r
  have hEq : leafOasP = leafP :=
    (Classical.choose_spec
      (unique_target_terminal_for_source_marker hb g P LP hTP r)).2
        leafOasP hPrefix
  exact congrArg Subtype.val hEq

/-- For two supported, same-complete-signature targets whose finite trees
agree, the ACTUAL target-terminal component of the reduced record agrees
at every D₂ coordinate, for ANY Γ₁/Γ₂ split. No letter comparison is
used in this geometric result. -/
theorem terminalReducedTargetRecord_fst_eq_of_same_tree
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
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (terminalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 i).1 =
      (terminalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1 i).1 := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hLeaf : (targetLeafForSourceMarker hb g O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO HO)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f O hSO) r).1 =
    (targetLeafForSourceMarker hb g P
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g P cutP HP)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f P hSP) r).1 :=
    targetLeaf_eq_of_same_tree hb g O P
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO HO)
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g P cutP HP)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f O hSO)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
        g f P hSP) hTree r
  have hO := terminalReducedTargetRecord_marker_eq_targetLeaf
    hb g f fallback O cutO HO hSO gamma1 r
  have hP := terminalReducedTargetRecord_marker_eq_targetLeaf
    hb g f fallback P cutP HP hSP gamma1 r
  rw [← hi]
  exact hO.trans (hLeaf.trans hP.symm)

/-- When Γ₁ is empty, all optional residual letters are absent. Therefore
equality of the target trees already gives equality of the WHOLE
canonical terminal record, including all Γ₂ coordinates. -/
theorem terminalReducedTargetRecord_eq_of_same_tree_gamma2_only
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
    (hTree : O.tree.toFinset = P.tree.toFinset) :
    terminalReducedTargetRecord hb g f fallback O cutO HO hSO
      (fun _ => false) =
    terminalReducedTargetRecord hb g f fallback P cutP HP hSP
      (fun _ => false) := by
  funext i
  apply Prod.ext
  · exact terminalReducedTargetRecord_fst_eq_of_same_tree
      hb g f fallback O P cutO cutP HO HP hSO hSP
        (fun _ => false) hTree i
  · simp [terminalReducedTargetRecord,
      ForwardQFinalCanonicalReducedRecord.canonicalReducedTargetRecord]

/-- Genuine cross-target, same-tree colour equality for Γ₁ = ∅.
The remaining conditions are precisely the existing genuine enlarged
eligible-target hypotheses, Definition-11 c-goodness and the smooth
total Q-pullback; no full starred-span monochromaticity is assumed. -/
theorem eligible_targets_color_eq_of_same_tree_gamma2_only
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : ForwardQFinalTargetObservation.Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput
      g.core → γ)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 =
        color (ForwardQFinalTargetObservation.observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)))
    (hsmooth : ∀ x y : ForwardQEnlargedConstantWords.EnlargedInput
      g.core,
      MixedProduct.SmoothRelated (fun _ => false) x y →
        total x = total y)
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
    (hTree : O.tree.toFinset = P.tree.toFinset) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  apply eligible_targets_color_eq_of_terminal_reduced_record
    hb g f fallback hα color total (fun _ => false)
    hagree hsmooth hgood O P cutO cutP HO HP
      hspanO hspanP hSO hSP
  exact terminalReducedTargetRecord_eq_of_same_tree_gamma2_only
    hb g f fallback O P cutO cutP HO HP hSO hSP hTree

end DualTree.ForwardQFinalSameTreeGamma2
