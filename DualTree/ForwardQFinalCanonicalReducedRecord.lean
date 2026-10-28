import DualTree.ForwardQFinalEnlargedReducedGoodTransfer
import DualTree.ForwardQFinalEnlargedConditionalStarred
import DualTree.ForwardQFinalEnlargedTargetD2Order

/-!
# Explicit corrected target records without arbitrary preimage choices

The earlier c-good transfer selected an arbitrary starred Q preimage
of each target using Classical.choose. Its residual bulletRecord
therefore looks formally dependent on this choice.

For the genuine enlarged local word we already HAVE an explicit
coherentTargetInput, with its real D₂-starred certificate derived
from target skewness. We package exactly that explicit witness and
derive its complete target observation equality.

Its bulletRecord is determined by the target terminals and the
canonical encoder at the corresponding actual local variable roots:
there is no choice of an arbitrary Q preimage. The reduced Γ₁/Γ₂
record retains only the marked local roots and the encoded letter
at Γ₁ indices.

A c-good, smooth total Q pullback consequently factors target
colours through this explicit record. This avoids dependence on
Classical.choose in the RECORD itself, but does not assert that
those records agree for arbitrary targets with the same signature,
nor does it establish a new finite Ramsey theorem.
-/

namespace DualTree.ForwardQFinalCanonicalReducedRecord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetObservation
open ForwardQFinalEnlargedTargetInput
open ForwardQFinalEnlargedTargetD2Order
open ForwardQFinalEnlargedConditionalStarred
open ForwardQFinalFullSignatureRootTransport

/-- Explicit genuine enlarged starred Q witness with the SAME
underlying coherent mixed input, using only the automatic D₂
order from target skewness. No arbitrary existential witness. -/
noncomputable def canonicalStarredTargetInput
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
        g.core f (m + q)) :
    ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback :=
  ⟨coherentTargetInput hb g f fallback O cutO H hSupport,
    coherentTargetInput_isStarred_of_order
      hb g f fallback O cutO H hSupport
      (targetD2Ordered_of_target_skew
        hb g f fallback O cutO H hSupport)⟩

/-- The named explicit canonical witness belongs to the REAL
enlarged local mixed-product word span. -/
theorem canonicalStarredTargetInput_mem_span
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
        g.core f (m + q)) :
    (canonicalStarredTargetInput
      hb g f fallback O cutO H hSupport).1 ∈ f.span :=
  coherentTargetInput_mem_mixed_span hb g f fallback O cutO H hSupport

/-- The explicit, not existentially chosen, Q witness has the
ENTIRE representation-independent rooted target observation.
It reproduces the finite support and complete dependent word,
not just one evaluation. -/
theorem canonicalStarredTargetInput_observe_eq
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
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) :
    observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
      hb g fallback
      (canonicalStarredTargetInput
        hb g f fallback O cutO H hSupport)) = observe O := by
  classical
  let w := canonicalStarredTargetInput
    hb g f fallback O cutO H hSupport
  have htree :
      nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w.1) =
      O.tree.toFinset :=
    ForwardQFinalGenericTargetNodeSet.coherent_enlarged_target_Q_node_set_eq
      hb g f fallback O cutO H hSupport
  have hset :
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree.toFinset = O.tree.toFinset := by
    change
      (nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w.1)).toList.toFinset =
      O.tree.toFinset
    simpa using htree
  have hU :
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord hb g fallback w)
  have hO : O.tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup O
  have hperm :
      List.Perm
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w).tree O.tree :=
    List.perm_of_nodup_nodup_toFinset_eq hU hO hset
  apply observe_Q_eq_target_of_tree_perm_and_word_reindexed
    hb g fallback O cutO H w hperm
  intro s
  change Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
    (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w.1 s) =
    O.word.word s
  exact ForwardQFinalEnlargedTargetWholeWord.coherent_target_Q_matches_full_word
    hb g f fallback O cutO H hα hspan hSupport s

/-- Explicit residual record of an eligible target: genuine
local selected D₂ roots together with the canonical encoded
target symbol only at Γ₁ coordinates. No arbitrary choice of
a Q preimage or its dependent input representation appears. -/
noncomputable def canonicalReducedTargetRecord
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
      (BoundedNode b (k - (m + 1)) ×
        Option (Sum α (Fin (m + 1)))) :=
  fun i =>
    let p := targetBulletPoint hb g f O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H) hSupport i
    (p, if gamma1 i then
      some (ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
        hb g O cutO H fallback i.1 p) else none)

/-- At an actual selected D₂ point, the corresponding local
component WORD has a variable symbol rooted there. Its genuine
enlarged-Q encoder therefore yields exactly the encoded target
symbol used in the explicit residual record. -/
theorem canonicalStarredTargetInput_bullet_letter
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
    (i : MixedProduct.BulletIndex (kind g.core)) :
    ((canonicalStarredTargetInput
      hb g f fallback O cutO H hSupport).1).words
        i.1
        (((canonicalStarredTargetInput
          hb g f fallback O cutO H hSupport).1).bulletPoint i) =
      ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
        hb g O cutO H fallback i.1
          (targetBulletPoint hb g f O
            (ForwardQFinalFullSignature.complete_signature_implies_literal
              hb g O cutO H) hSupport i) := by
  let p := targetBulletPoint hb g f O
    (ForwardQFinalFullSignature.complete_signature_implies_literal
      hb g O cutO H) hSupport i
  have hp : p ∈ (f.vector.components i.1).support :=
    targetBulletPoint_mem_component_support
      hb g f O (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H) hSupport i
  let v : (f.vector.components i.1).Vars := ⟨p, hp⟩
  have hroot :
      (f.vector.components i.1).word p = Sum.inr v :=
    (f.vector.components i.1).toVariableWord.atRoot v
  change (coherentTargetInput hb g f fallback O cutO H hSupport).words i.1 p =
    ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
      hb g O cutO H fallback i.1 p
  simpa [coherentTargetInput, hroot, v]

/-- The explicit reduced record is EXACTLY the reduced
bullet record of the concrete corrected starred input. This
is the key bridge to the existing Γ₂-letter normalization
and Definition 11/21 factorization theorem. -/
theorem canonicalReducedTargetRecord_eq_input_record
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
    canonicalReducedTargetRecord hb g f fallback O cutO H
      hSupport gamma1 i =
    (let x := (canonicalStarredTargetInput
      hb g f fallback O cutO H hSupport).1
     (x.bulletPoint i,
      if gamma1 i then
        some (x.words i.1 (x.bulletPoint i)) else none)) := by
  dsimp [canonicalReducedTargetRecord]
  rw [← canonicalStarredTargetInput_bullet_letter
    hb g f fallback O cutO H hSupport i]
  rfl

/-- The TRUE c-good plus smoothness target canonization with a
concrete, choice-independent-on-preimage residual record.
Equality is required only of the marked D₂ roots and the Γ₁
encoded observed letters—not of Γ₂ letters or full local
words. It does not assert full target monochromaticity. -/
theorem eligible_targets_color_eq_of_canonical_reduced_record
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput g.core → γ)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 =
        color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)))
    (hsmooth : ∀ x y : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      MixedProduct.SmoothRelated gamma1 x y → total x = total y)
    (hgood : MixedProduct.Good total f)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature hb g P cutP)
    (hspanO : O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hspanP : P.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSuppO : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hSuppP : ∀ t : Node b, t ∈ P.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hrec :
      canonicalReducedTargetRecord hb g f fallback O cutO HO hSuppO gamma1 =
      canonicalReducedTargetRecord hb g f fallback P cutP HP hSuppP gamma1) :
    color (observe O) = color (observe P) := by
  let x := canonicalStarredTargetInput
    hb g f fallback O cutO HO hSuppO
  let y := canonicalStarredTargetInput
    hb g f fallback P cutP HP hSuppP
  have hx : x.1 ∈ f.span :=
    canonicalStarredTargetInput_mem_span hb g f fallback O cutO HO hSuppO
  have hy : y.1 ∈ f.span :=
    canonicalStarredTargetInput_mem_span hb g f fallback P cutP HP hSuppP
  have hpts :
      ∀ i : MixedProduct.BulletIndex (kind g.core),
        x.1.bulletPoint i = y.1.bulletPoint i := by
    intro i
    have h := congrFun hrec i
    rw [canonicalReducedTargetRecord_eq_input_record,
      canonicalReducedTargetRecord_eq_input_record] at h
    exact congrArg Prod.fst h
  have hletters :
      ∀ i : MixedProduct.BulletIndex (kind g.core),
        gamma1 i = true →
          x.1.words i.1 (x.1.bulletPoint i) =
          y.1.words i.1 (y.1.bulletPoint i) := by
    intro i hγ
    have h := congrArg Prod.snd (congrFun hrec i)
    rw [canonicalReducedTargetRecord_eq_input_record,
      canonicalReducedTargetRecord_eq_input_record] at h
    simp only [hγ, ite_true] at h
    exact Option.some.inj h
  have hxy : total x.1 = total y.1 :=
    MixedProduct.good_smooth_color_eq_of_reduced_bullet_record
      f total gamma1 hgood hsmooth (Sum.inl fallback)
      x.1 y.1 hx hy hpts hletters
  calc
    color (observe O) =
      color (observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback x)) :=
        congrArg color
          (canonicalStarredTargetInput_observe_eq
            hb g f fallback O cutO HO hα hspanO hSuppO).symm
    _ = total x.1 := (hagree x).symm
    _ = total y.1 := hxy
    _ = color (observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback y)) := hagree y
    _ = color (observe P) :=
        congrArg color
          (canonicalStarredTargetInput_observe_eq
            hb g f fallback P cutP HP hα hspanP hSuppP)
end DualTree.ForwardQFinalCanonicalReducedRecord
