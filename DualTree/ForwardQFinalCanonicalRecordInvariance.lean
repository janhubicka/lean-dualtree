import DualTree.ForwardQFinalCanonicalReducedRecord

/-!
# Corrected target residual record is independent of the Ramsey word

The target-side D₂ marker points selected by the genuine enlarged
Q preimage are defined using the particular post-Ramsey local
variable word f, because the proof must check membership in its
actual local supports. Their GEOMETRIC positions, however, are
unique: at each original source marker they project to the same
unique terminal of the target tree O.

Two local enlarged Ramsey words f₁ and f₂ for the SAME source
frame may have different variable supports, dimensions and fixed
letters. If the target O is in the true height-budgeted final
support for BOTH, then their selected D₂ local points are
equal by injectivity of the fixed complete-T cone projection.

Consequently the explicit reduced Γ₁/Γ₂ target record depends
only on O, its corrected complete signature, the frame and the
canonical output encoder; it does NOT depend on which admissible
local Ramsey word was used to discover the same target terminals.
This is the invariance needed to formulate the subsequent
induction without choosing a different residual observable
at every mixed-product refinement.
-/

namespace DualTree.ForwardQFinalCanonicalRecordInvariance

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalEnlargedTargetInput
open ForwardQFinalCanonicalReducedRecord

/-- The unique selected D₂ local point above each target
terminal is independent of the genuine enlarged local word
and its rank parameter, as long as both height budgets
actually contain the target tree. -/
theorem targetBulletPoint_eq_across_enlarged_local_words
    {b n l k m q₁ q₂ : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f₁ : LocalMixedWord g.core q₁ (Sum α (Fin (m + 1))))
    (f₂ : LocalMixedWord g.core q₂ (Sum α (Fin (m + 1))))
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hS₁ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₁ (m + q₁))
    (hS₂ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₂ (m + q₂))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    targetBulletPoint hb g f₁ O L hS₁ i =
      targetBulletPoint hb g f₂ O L hS₂ i := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hp₁ :=
    ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint_projection
      hb g f₁ O L hS₁ r
  have hp₂ :=
    ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint_projection
      hb g f₂ O L hS₂ r
  have hleaf :
      (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
        hb g O L
          (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
            g f₁ O hS₁) r).1 =
      (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
        hb g O L
          (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
            g f₂ O hS₂) r).1 := rfl
  have hproj :
      (projected g.core
        ⟨i.1, targetBulletPoint hb g f₁ O L hS₁ i⟩).1 =
      (projected g.core
        ⟨i.1, targetBulletPoint hb g f₂ O L hS₂ i⟩).1 := by
    change
      (projected g.core
        ⟨i.1, ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint
          hb g f₁ O L hS₁ r⟩).1 =
      (projected g.core
        ⟨i.1, ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint
          hb g f₂ O L hS₂ r⟩).1
    rw [← hi]
    exact hp₁.trans (hleaf.trans hp₂.symm)
  apply ForwardQFinalRefinementRoots.projectLocal_injective g.core i.1
  apply Subtype.ext
  exact hproj

/-- The deterministic target Γ₁/Γ₂ reduced record is invariant
under changing the entire genuinely enlarged local Ramsey
variable word and its local dimension q, provided the same
target remains genuinely supported. Auxiliary CONSTANTS may
change freely: only the unique target terminal locations and
canonical encoding are used in the record.

This is an equality of complete finite residual records,
not an equality of the two local word spans or a claim of
unrestricted reverse coverage. -/
theorem canonicalReducedTargetRecord_eq_across_local_words
    {b n l k m q₁ q₂ : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f₁ : LocalMixedWord g.core q₁ (Sum α (Fin (m + 1))))
    (f₂ : LocalMixedWord g.core q₂ (Sum α (Fin (m + 1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hS₁ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₁ (m + q₁))
    (hS₂ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₂ (m + q₂))
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    canonicalReducedTargetRecord hb g f₁ fallback O cutO H
      hS₁ gamma1 =
    canonicalReducedTargetRecord hb g f₂ fallback O cutO H
      hS₂ gamma1 := by
  funext i
  have hpoint :
      targetBulletPoint hb g f₁ O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO H) hS₁ i =
      targetBulletPoint hb g f₂ O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO H) hS₂ i :=
    targetBulletPoint_eq_across_enlarged_local_words
      hb g f₁ f₂ O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H) hS₁ hS₂ i
  dsimp [canonicalReducedTargetRecord]
  rw [hpoint]


/-- Even the apparent choice of target cut in the explicit
Γ₁ reduced record is not a genuine ambiguity: the COMPLETE
corrected signature forces that cut to equal the source cut.
Thus the reduced record does not depend on the signature
proof or on a separate maximal-interior-cut witness. -/
theorem canonicalReducedTargetRecord_cut_independent
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutP)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    canonicalReducedTargetRecord hb g f fallback O cutO HO
      hSupport gamma1 =
    canonicalReducedTargetRecord hb g f fallback O cutP HP
      hSupport gamma1 := by
  have hcutO :=
    ForwardQFinalFullSignature.complete_signature_forces_same_cut
      hb g O cutO HO
  have hcutP :=
    ForwardQFinalFullSignature.complete_signature_forces_same_cut
      hb g O cutP HP
  subst cutO
  subst cutP
  rfl

end DualTree.ForwardQFinalCanonicalRecordInvariance
