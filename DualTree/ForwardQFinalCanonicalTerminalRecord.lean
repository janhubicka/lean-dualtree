import DualTree.ForwardQFinalCanonicalRecordInvariance

/-!
# Express the corrected residual D₂ record on target TREE terminals

The explicit reduced record now has no arbitrary Q-preimage choice
and is stable across supported local Ramsey refinements. Its
first component is still written as a LOCAL D₂ address z_i,
rather than the actual target-tree terminal t_i=P_i(z_i).

Here we project each marked local address into the fixed
complete-T ambient tree. The projected coordinate is the
UNIQUE target terminal above the corresponding original source
marker, independently of local alphabet values. Because
P_i is injective on its true local cone, equality of these
output-facing terminal records is EQUIVALENT to equality
of the earlier local address records.

Consequently the c-good/smooth target-colour factorization
can be expressed directly in terms of actual target-terminal
nodes and canonical enlarged letters at the Γ₁ markers.
This is an interface toward Definition 24, NOT a proof that
its published canonical selector equals the corrected selector
or that the terminal record is constant on a Ramsey subspace.
-/

namespace DualTree.ForwardQFinalCanonicalTerminalRecord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCanonicalReducedRecord

/-- The output-facing residual target record:
one GENUINE target terminal in the ambient homogeneous tree
at every selected D₂ index, and an encoded observed letter
only at Γ₁ indices. It is a projection of the already
verified local reduced record, not a new arbitrary choice. -/
noncomputable def terminalReducedTargetRecord
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
    MixedProduct.BulletIndex (kind g.core) →
      (Node b × Option (Sum α (Fin (m + 1)))) :=
  fun i =>
    let r := canonicalReducedTargetRecord hb g f fallback O cutO H
      hSupport gamma1 i
    ((projected g.core ⟨i.1,r.1⟩).1,r.2)

/-- The terminal recorded at the original source marker r is
EXACTLY the unique target O terminal above that marker. This
does not depend on arbitrary enumeration of O.tree, the
local word's fixed auxiliary constants or an arbitrary Q
preimage witness. -/
theorem terminalReducedTargetRecord_marker_eq_targetLeaf
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
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    (terminalReducedTargetRecord hb g f fallback O cutO H
      hSupport gamma1
      (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
    (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
      hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO H)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSupport) r).1 := by
  have h := ForwardQFinalEnlargedTargetInput.coherentTargetInput_markedProjection_eq_targetLeaf
    hb g f fallback O cutO H hSupport r
  change
    (projected g.core
      ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
        ForwardQFinalEnlargedTargetInput.targetBulletPoint
          hb g f O
            (ForwardQFinalFullSignature.complete_signature_implies_literal
              hb g O cutO H)
            hSupport
            (ForwardQMarkerCoverage.bulletForMarker g.core r)⟩).1 = _ at h
  exact h

/-- Comparing target-rooted terminal records is equivalent
to comparing the actual reduced LOCAL D₂ records: equality
of P_i(z_i) determines z_i by injectivity of the same fixed
complete-T projection at every index, and the Γ₁ letters
are literally the same in the two representations. -/
theorem terminalReducedRecord_eq_iff_localRecord_eq
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
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    terminalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      terminalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1 ↔
    canonicalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      canonicalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1 := by
  constructor
  · intro hterm
    funext i
    let rO := canonicalReducedTargetRecord
      hb g f fallback O cutO HO hSO gamma1 i
    let rP := canonicalReducedTargetRecord
      hb g f fallback P cutP HP hSP gamma1 i
    have hi := congrFun hterm i
    change
      ((projected g.core ⟨i.1,rO.1⟩).1,rO.2) =
      ((projected g.core ⟨i.1,rP.1⟩).1,rP.2) at hi
    have hproj :
        (projected g.core ⟨i.1,rO.1⟩).1 =
          (projected g.core ⟨i.1,rP.1⟩).1 :=
      congrArg Prod.fst hi
    have hlocal : rO.1 = rP.1 := by
      apply ForwardQFinalRefinementRoots.projectLocal_injective
        g.core i.1
      apply Subtype.ext
      exact hproj
    have hletter : rO.2 = rP.2 :=
      congrArg
        (fun p : Node b × Option (Sum α (Fin (m + 1))) => p.2) hi
    exact Prod.ext hlocal hletter
  · intro hlocal
    funext i
    have hi := congrFun hlocal i
    exact congrArg
      (fun r : BoundedNode b (k - (m + 1)) ×
          Option (Sum α (Fin (m + 1))) =>
        ((projected g.core ⟨i.1,r.1⟩).1,r.2)) hi

/-- The corrected actual Q target colour comparison may be
stated entirely on the target-terminal record. Equal terminal
nodes and Γ₁ encoded letters suffice under verified
Definition-11 c-goodness and Definition-21 smoothness.

It is not necessary to compare local D₂ addresses or any
Γ₂ letters in the statement; the injective geometric transport
and the existing canonical reduced-colour theorem supply
those details. -/
theorem eligible_targets_color_eq_of_terminal_reduced_record
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : ForwardQFinalTargetObservation.Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput
      g.core → γ)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 =
        color (ForwardQFinalTargetObservation.observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)))
    (hsmooth : ∀ x y : ForwardQEnlargedConstantWords.EnlargedInput
      g.core,
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
    (hrecord :
      terminalReducedTargetRecord hb g f fallback O cutO HO hSO gamma1 =
      terminalReducedTargetRecord hb g f fallback P cutP HP hSP gamma1) :
    color (ForwardQFinalTargetObservation.observe O) =
      color (ForwardQFinalTargetObservation.observe P) := by
  apply eligible_targets_color_eq_of_canonical_reduced_record
    hb g f fallback hα color total gamma1 hagree hsmooth hgood
      O P cutO cutP HO HP hspanO hspanP hSO hSP
  exact (terminalReducedRecord_eq_iff_localRecord_eq
    hb g f fallback O P cutO cutP HO HP hSO hSP gamma1).1 hrecord

end DualTree.ForwardQFinalCanonicalTerminalRecord
