import DualTree.ForwardQFinalEnlargedTargetLocalFibres
import DualTree.ForwardQFinalPolymorphicTargetD2
import DualTree.ForwardQLiteralMarkerLeafEquiv
import DualTree.ForwardQFinalOutputProjectedEncoder

/-!
# A coherent actual enlarged mixed-span input carrying target terminals

For the genuine post-Corollary-22 local Ramsey word with alphabet
β = α ⊕ Fin (m+1), the inverse D₂ geometry is independent of the
constant alphabet: each original literal source marker identifies
one actual local variable root whose projection is exactly the
required target O terminal.

To reconstruct the ordinary coordinate words, keep EVERY fixed
β constant literally intact and assign one β letter to each
genuine local component variable root. The chosen letter encodes
the target O dependent symbol at P_i(v), using the actual
visible-ancestor R_i decoder. Thus all occurrences of one
local variable use the SAME chosen β letter; no independent
positionwise choices or illegal constant-lifts are introduced.

This file establishes the exact target D₂ marked projections,
the real enlarged mixed-span membership and uniformity of this
target-input construction. The selected target D₂ tuple's global
starred order and exact full Q-output word remain separate.
-/

namespace DualTree.ForwardQFinalEnlargedTargetInput

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalPolymorphicTargetD2
open ForwardQFinalFullSignature

/-- The requested target terminal's true local address at a
genuine sorted source D₂ bullet coordinate, for an arbitrary
local alphabet β independent of the target alphabet α. -/
noncomputable def targetBulletPoint
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    BoundedNode b (k-(m+1)) :=
  ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint
    hb g f O L hSupport
    ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
      g.core).symm i)

/-- The actual target-selected D₂ point is in the local variable
support of the exact source bullet coordinate. In particular it
is legal for the genuine enlarged mixed Ramsey word's span. -/
theorem targetBulletPoint_mem_component_support
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    targetBulletPoint hb g f O L hSupport i ∈
      (f.vector.components i.1).support := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hroot :=
    ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint_mem_component_support
      hb g f O L hSupport r
  change
    ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint
      hb g f O L hSupport r ∈
    (f.vector.components i.1).support
  rw [← hi]
  exact hroot

/-- The honest target-selected enlarged mixed-product input.

Its ordinary words are genuine local β-word evaluations:
FIXED auxiliary constants are preserved, while each actual local
variable v is uniformly replaced by ONE chosen β letter encoding
O's symbol at P_i(v). Its bullet points are the exact target D₂
terminals. There are no impossible D₁ coordinates in this frame. -/
noncomputable def coherentTargetInput
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    ForwardQEnlargedConstantWords.EnlargedInput g.core where
  words := fun i z =>
    match (f.vector.components i).word z with
    | Sum.inl a => a
    | Sum.inr v =>
        ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
          hb g O cutO H fallback i v.1
  upPoint := fun i =>
    False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  bulletPoint :=
    targetBulletPoint hb g f O
      (complete_signature_implies_literal hb g O cutO H) hSupport

/-- A genuine source-facing full MIXED span witness, not merely
membership in the componentwise vector span: selected D₂ points
are actual local variable roots, fixed β constants remain fixed,
and each local variable fibre gets one uniform β letter. -/
theorem coherentTargetInput_mem_mixed_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    coherentTargetInput hb g f fallback O cutO H hSupport ∈
      f.span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨(fun v => ForwardQFinalOutputProjectedEncoder.encodeProjectedOutputSymbol
        hb g O cutO H fallback i v.1), ?_⟩
    funext z
    cases hz : (f.vector.components i).word z with
    | inl a =>
        simp [coherentTargetInput, SpanAudit.eval,
          SpanAudit.evalSymbol, hz]
    | inr v =>
        simp [coherentTargetInput, SpanAudit.eval,
          SpanAudit.evalSymbol, hz]
  · intro i
    exact False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  · intro i
    exact targetBulletPoint_mem_component_support
      hb g f O
      (complete_signature_implies_literal hb g O cutO H)
      hSupport i

/-- The selected genuine local D₂ coordinate at the original
marker r projects to its UNIQUE target O terminal, independently
of every ordinary word symbol or auxiliary constant choice. -/
theorem coherentTargetInput_markedProjection_eq_targetLeaf
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    (markedProjection g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (coherentTargetInput hb g f fallback O cutO H hSupport))
      (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
    (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
      hb g O (complete_signature_implies_literal hb g O cutO H)
      (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T g f O hSupport)
      r).1 := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  have hr : e.symm
      (ForwardQMarkerCoverage.bulletForMarker g.core r) = r :=
    e.symm_apply_apply r
  change
    (projected g.core
      ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
        targetBulletPoint hb g f O
          (complete_signature_implies_literal hb g O cutO H)
          hSupport
          (ForwardQMarkerCoverage.bulletForMarker g.core r)⟩).1 = _
  change
    (projected g.core
      ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
        ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint hb g f O
          (complete_signature_implies_literal hb g O cutO H)
          hSupport (e.symm
            (ForwardQMarkerCoverage.bulletForMarker g.core r))⟩).1 = _
  rw [hr]
  exact ForwardQFinalPolymorphicTargetD2.targetD2LocalPoint_projection
    hb g f O (complete_signature_implies_literal hb g O cutO H)
    hSupport r

/-- All occurrences of the SAME genuine local variable use one
certified enlarged letter in the target-selected mixed point.
Fixed auxiliary constants remain unchanged by this construction. -/
theorem coherentTargetInput_constant_on_local_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k-(m+1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    (coherentTargetInput hb g f fallback O cutO H hSupport).words i z =
    (coherentTargetInput hb g f fallback O cutO H hSupport).words i v.1 := by
  have hroot := (f.vector.components i).toVariableWord.atRoot v
  simp [coherentTargetInput, hz, hroot]

end DualTree.ForwardQFinalEnlargedTargetInput
