import DualTree.ForwardQFinalPolymorphicTargetD2
import DualTree.ForwardQFinalInducedStarredPoint

/-!
# Full enlarged-alphabet mixed input induced by a final-root assignment

For the TRUE post-Corollary-22 mixed variable word over
α ⊕ Fin(m+1), each selected local variable represents a NEW final
ambient root, and its value in a desired final evaluation is an α
letter. Auxiliary fixed constants must remain fixed auxiliary
letters in the generated mixed input, to be decoded by Q through
R_i, and not collapsed to an arbitrary α letter.

This file constructs a real enlarged-alphabet mixed-product element:
each coordinate word evaluates the actual local word with one
original α letter for each independent local variable; all auxiliary
fixed constants are preserved. D₂ marker points are the canonical
zero-intrinsic-rank roots, whose order follows vector completeness.
Thus the resulting point is in the ACTUAL starred portion of the
enlarged mixed Ramsey span when q>0.

The early source-root assignments σ and τ must agree on the fixed
old roots. Under that explicit condition, the visible-ancestor
decoder R_i and its lifted final-root version have identical
evaluations. The final projected-root comparison uses this fact
in the auxiliary-constant case, without a forbidden map from the
entire enlarged alphabet into original α.

This is the forward evaluation step of the corrected construction,
not a reverse-starred target preimage or the complete Lemma 27.
-/

namespace DualTree.ForwardQFinalEnlargedInducedEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedLocalSymbols

/-- The necessary agreement on original source roots retained in
the final support. It does not freeze any genuinely new projected
variable root. -/
def OldRootAssignmentCompatible
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α) : Prop :=
  ∀ v : g.core.source.word.Vars,
    σ (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot g f v) = τ v

/-- Evaluating a genuine fixed auxiliary letter j after the lifted
R_i final-variable decoder is EXACTLY evaluating the original
old-source R_i decoder, under the legitimate old-root compatibility
condition. No separate auxiliary-to-α constant decoder exists. -/
theorem decodeAuxIntoFinal_eval_eq_source
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (hcompat : OldRootAssignmentCompatible g f σ τ)
    (i : Index g.core) (j : Fin (m+1)) :
    SpanAudit.evalSymbol σ (decodeAuxIntoFinal g f fallback i j) =
      SpanAudit.evalSymbol τ
        (ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j) := by
  cases h : ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j with
  | inl a =>
      simp [decodeAuxIntoFinal, h, SpanAudit.evalSymbol]
  | inr v =>
      simpa [decodeAuxIntoFinal, h, SpanAudit.evalSymbol,
        OldRootAssignmentCompatible] using hcompat v

/-- One ORIGINAL alphabet letter is assigned to every actual
local variable root, and the same enlarged letter is used at
all occurrences of that variable. Only genuinely rank-selected
roots depend on the final assignment σ; excluded high-band
roots receive the documented fallback. -/
noncomputable def chosenLocalLetter
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars) :
    Sum α (Fin (m+1)) := by
  classical
  exact Sum.inl
    (if h : (⟨i,v.1⟩ : LocalAddress g.core) ∈
        selectedLocalRoots g.core f (m+q) then
      σ (ForwardQFinalSelectedVariableTransport.selectedBoundedRoot
        g f ⟨⟨i,v.1⟩,h⟩)
    else fallback)

/-- Assemble the ACTUAL enlarged mixed-product input, not the
constant-lift of some unrelated original-alphabet mixed point.
Each word is a genuine evaluation of the local β-valued variable
word, so its fixed auxiliary constants are literally retained. -/
noncomputable def enlargedInducedInput
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α) :
    ForwardQEnlargedConstantWords.EnlargedInput g.core where
  words := fun i => SpanAudit.eval
    (f.vector.components i).word (chosenLocalLetter g f fallback σ i)
  upPoint := fun i =>
    False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  bulletPoint := fun i =>
    ForwardQFinalLocalRoots.localRoot g.core f i.1

/-- This is an actual point of the given enlarged mixed Ramsey
word span, including the genuine D₂ support-membership conditions.
The auxiliary constants are not independently adjusted: they remain
as fixed letters in their original local component words. -/
theorem enlargedInducedInput_mem_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α) :
    enlargedInducedInput g f fallback σ ∈ f.span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨chosenLocalLetter g f fallback σ i, rfl⟩
  · intro i
    exact False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  · intro i
    exact ForwardQFinalLocalRoots.localRoot_mem g.core f i.1

/-- The selected D₂ positions are the true intrinsic-zero
component roots; genuine vector-q-completeness orders their
lengths. The original alphabet of these component words is
irrelevant to the singleton starred order. -/
theorem enlargedInducedInput_bullet_lengths_ordered
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin(m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    ForwardQIndexedTRanks.BulletLengthsOrdered
      g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (enlargedInducedInput g f fallback σ)) := by
  intro i j hij
  change
    (ForwardQFinalLocalRoots.localRoot g.core f i.1).1.length ≤
      (ForwardQFinalLocalRoots.localRoot g.core f j.1).1.length
  let z := ForwardQFinalLocalRoots.localRoot g.core f i.1
  let w := ForwardQFinalLocalRoots.localRoot g.core f j.1
  have hz :
      z.1 ∈ (f.vector.components i.1).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i.1).support.map (fun u => u.1)
    exact List.mem_map.mpr
      ⟨z,ForwardQFinalLocalRoots.localRoot_mem g.core f i.1,rfl⟩
  have hw :
      w.1 ∈ (f.vector.components j.1).toVariableWord.supportNodes := by
    change w.1 ∈ (f.vector.components j.1).support.map (fun u => u.1)
    exact List.mem_map.mpr
      ⟨w,ForwardQFinalLocalRoots.localRoot_mem g.core f j.1,rfl⟩
  exact ForwardQFinalVectorOrdering.local_lengths_le_of_equal_level
    g.core f i.1 j.1 hij 0 hq z w hz hw
    (ForwardQFinalLocalRoots.localRoot_height_zero g.core f i.1)
    (ForwardQFinalLocalRoots.localRoot_height_zero g.core f j.1)

/-- Every final-root assignment therefore produces an actual
enlarged corrected STARRED mixed input in the genuine enlarged
mixed-variable-word span, rather than only an arbitrary mixed point. -/
noncomputable def enlargedInducedStarredInput
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback :=
  ⟨enlargedInducedInput g f fallback σ,
    (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (enlargedInducedInput g f fallback σ))).2
      (enlargedInducedInput_bullet_lengths_ordered
        g f fallback σ hq)⟩

/-- The actual enlarged starred point belongs to the real
mixed Ramsey span with no hidden constant-lift restriction. -/
theorem enlargedInducedStarredInput_mem_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin(m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    (enlargedInducedStarredInput g f fallback σ hq).1 ∈ f.span :=
  enlargedInducedInput_mem_span g f fallback σ

/-- The actual local coordinate evaluation is definitional:
original and auxiliary FIXED constants remain unaltered, while
local variables receive their single selected value. -/
theorem enlargedInducedInput_word_at
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    (enlargedInducedInput g f fallback σ).words i z =
      SpanAudit.evalSymbol
        (chosenLocalLetter g f fallback σ i)
        ((f.vector.components i).word z) := by
  rfl

end DualTree.ForwardQFinalEnlargedInducedEvaluation
