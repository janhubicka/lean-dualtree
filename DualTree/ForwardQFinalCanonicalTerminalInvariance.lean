import DualTree.ForwardQFinalCanonicalTerminalRecord

/-!
# The corrected terminal reduced record is independent of local refinements

The previous module transports the chosen D₂ local coordinates to actual
nodes of the target tree. We now show this OUTPUT-FACING record is independent
of the particular enlarged-alphabet local Ramsey word, even when its
dimension and fixed auxiliary constants change, provided the target really
lies in both resulting finite final supports.

We also remove dependence on the cut certificate. These results let a later
Ramsey iteration compare the same terminal observable across refinements.
They neither make the residual record constant across different targets nor
provide the missing finite smooth Ramsey witness or the printed selector.
-/

namespace DualTree.ForwardQFinalCanonicalTerminalInvariance

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalCanonicalTerminalRecord

/-- Two genuinely enlarged local Ramsey words with potentially different
dimensions produce exactly the same output-facing terminal record for one
supported target. This also includes the Γ₁ auxiliary-letter field, not
just the locations of the target leaves. -/
theorem terminalReducedTargetRecord_eq_across_local_words
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
    terminalReducedTargetRecord hb g f₁ fallback O cutO H
      hS₁ gamma1 =
    terminalReducedTargetRecord hb g f₂ fallback O cutO H
      hS₂ gamma1 := by
  funext i
  have hi := congrFun
    (ForwardQFinalCanonicalRecordInvariance.canonicalReducedTargetRecord_eq_across_local_words
      hb g f₁ f₂ fallback O cutO H hS₁ hS₂ gamma1) i
  exact congrArg
    (fun r : BoundedNode b (k - (m + 1)) ×
        Option (Sum α (Fin (m + 1))) =>
      ((projected g.core ⟨i.1, r.1⟩).1, r.2)) hi

/-- The terminal record does not depend on which proof of the complete
corrected signature, or which apparent maximal interior cut, is supplied.
Complete-signature equality already forces the cut. -/
theorem terminalReducedTargetRecord_cut_independent
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
    terminalReducedTargetRecord hb g f fallback O cutO HO
      hSupport gamma1 =
    terminalReducedTargetRecord hb g f fallback O cutP HP
      hSupport gamma1 := by
  funext i
  have hi := congrFun
    (ForwardQFinalCanonicalRecordInvariance.canonicalReducedTargetRecord_cut_independent
      hb g f fallback O cutO cutP HO HP hSupport gamma1) i
  exact congrArg
    (fun r : BoundedNode b (k - (m + 1)) ×
        Option (Sum α (Fin (m + 1))) =>
      ((projected g.core ⟨i.1, r.1⟩).1, r.2)) hi

/-- Combine independence of Ramsey word and signature witness:
even simultaneous changes of local dimension and cut certificate
leave the output-facing residual target record fixed. -/
theorem terminalReducedTargetRecord_eq_across_words_and_cuts
    {b n l k m q₁ q₂ : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f₁ : LocalMixedWord g.core q₁ (Sum α (Fin (m + 1))))
    (f₂ : LocalMixedWord g.core q₂ (Sum α (Fin (m + 1))))
    (fallback : α)
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
    terminalReducedTargetRecord hb g f₁ fallback O cutO HO
      hS₁ gamma1 =
    terminalReducedTargetRecord hb g f₂ fallback O cutP HP
      hS₂ gamma1 := by
  calc
    terminalReducedTargetRecord hb g f₁ fallback O cutO HO hS₁ gamma1 =
      terminalReducedTargetRecord hb g f₂ fallback O cutO HO hS₂ gamma1 :=
      terminalReducedTargetRecord_eq_across_local_words
        hb g f₁ f₂ fallback O cutO HO hS₁ hS₂ gamma1
    _ = terminalReducedTargetRecord hb g f₂ fallback O cutP HP hS₂ gamma1 :=
      terminalReducedTargetRecord_cut_independent
        hb g f₂ fallback O cutO cutP HO HP hS₂ gamma1

end DualTree.ForwardQFinalCanonicalTerminalInvariance
