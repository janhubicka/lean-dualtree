import DualTree.ForwardQFinalTargetLeafIntrinsicRecord

/-!
# Proof independence of the direct target-leaf record

The direct corrected Lemma-27 target record uses no local Ramsey word.
It is defined from unique target leaves over fixed source markers,
whose existence was obtained using the corrected literal-signature
certificate and containment of O.tree in the ambient T.

Those certificates are PROPOSITIONS, not additional target data.
We first remove dependence on which evidence is supplied. Then the
verified equality of the previous local-support-dependent record
with the direct record gives an explicit theorem comparing arbitrary
genuinely enlarged local mixed words of different dimensions, different
fallback original letters and different complete-signature cut witnesses.

This proves stability of the exact rooted target record; it does
NOT assert existence of the required c-good Ramsey refinement or
constancy across different target trees.
-/

namespace DualTree.ForwardQFinalTargetLeafRecordInvariance

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetLeafIntrinsicRecord
open ForwardQFinalIntrinsicRootedTerminal

/-- The direct target-leaf/rooted-symbol record is independent of
the supplied proof of the SAME literal corrected signature and of
the supplied ambient-T containment proof. These are Prop-valued
witnesses, so they cannot affect the fixed target observation. -/
theorem targetLeafRootedRecord_certificate_independent
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L₁ L₂ : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT₁ hT₂ : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    targetLeafRootedRecord hb g O L₁ hT₁ gamma1 =
      targetLeafRootedRecord hb g O L₂ hT₂ gamma1 := by
  rfl

/-- A genuinely stronger invariance than merely keeping the LOCAL word
fixed: the original intrinsic target record cannot depend on which of
TWO enlarged local mixed Ramsey words supports the same target, even
if their local dimensions, original-alphabet fallback constants and
complete-signature certificates are all different. -/
theorem intrinsicRootedTargetRecord_eq_across_words_fallbacks_and_cuts
    {b n l k m q₁ q₂ : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f₁ : LocalMixedWord g.core q₁ (Sum α (Fin (m + 1))))
    (f₂ : LocalMixedWord g.core q₂ (Sum α (Fin (m + 1))))
    (fallback₁ fallback₂ : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutP)
    (hS₁ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₁ (m + q₁))
    (hS₂ : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f₂ (m + q₂))
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool) :
    intrinsicRootedTargetRecord hb g f₁ fallback₁ O cutO HO
      hS₁ gamma1 =
    intrinsicRootedTargetRecord hb g f₂ fallback₂ O cutP HP
      hS₂ gamma1 := by
  calc
    intrinsicRootedTargetRecord hb g f₁ fallback₁ O cutO HO hS₁ gamma1 =
      targetLeafRootedRecord hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f₁ O hS₁) gamma1 :=
      intrinsicRootedTargetRecord_eq_targetLeafRootedRecord
        hb g f₁ fallback₁ O cutO HO hS₁ gamma1
    _ = targetLeafRootedRecord hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutP HP)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f₂ O hS₂) gamma1 :=
      targetLeafRootedRecord_certificate_independent hb g O
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutO HO)
        (ForwardQFinalFullSignature.complete_signature_implies_literal
          hb g O cutP HP)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f₁ O hS₁)
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f₂ O hS₂) gamma1
    _ = intrinsicRootedTargetRecord hb g f₂ fallback₂ O cutP HP
        hS₂ gamma1 :=
      (intrinsicRootedTargetRecord_eq_targetLeafRootedRecord
        hb g f₂ fallback₂ O cutP HP hS₂ gamma1).symm

end DualTree.ForwardQFinalTargetLeafRecordInvariance
