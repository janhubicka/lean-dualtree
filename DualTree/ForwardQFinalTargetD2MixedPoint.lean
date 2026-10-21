import DualTree.ForwardQFinalTargetD2Point
import DualTree.ForwardQFinalInducedStarredPoint
import DualTree.ForwardQLiteralMarkerLeafEquiv

/-!
# Assemble exact target terminal D2 points into a local Ramsey span point

For each source R marker r, the selected targetD2LocalPoint(r) is an
actual variable root of the local component at bulletForMarker(r),
and its corrected projection is EXACTLY the unique target O terminal
associated to r.

The existing bijection from source literal markers to D2 bullet
indices therefore places these exact local points into ALL the
appropriate bullet coordinates of one genuine mixed-product point.
For its ordinary coordinate words and impossible D1 points we reuse
the already validated inducedPoint from the local mixed Ramsey span.

This gives an UNCONDITIONAL span-membership theorem for the local
mixed point with the requested target terminal positions, and a
pointwise exact marker-projection equality. In particular support
membership of the individual D2 points is no longer an obstacle.

The corrected W_* starred condition is an additional global
vector-one-completeness/order requirement on this specific D2 tuple.
We prove the precise conditional bridge but do NOT assert that this
condition follows from the other hypotheses. Full Q-object equality
and the dual-tree theorem remain unverified.
-/

namespace DualTree.ForwardQFinalTargetD2MixedPoint

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetD2Point

/-- Actual target leaf's chosen local tail at the D2 coordinate i,
using the canonical inverse from D2 bullets to ORIGINAL literal
source R markers. -/
noncomputable def targetBulletPoint
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    BoundedNode b (k - (m + 1)) :=
  targetD2LocalPoint hb g f O L hSupport
    ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
      g.core).symm i)

/-- Assemble a genuine corrected source-facing local mixed point:
all ordinary words come from a verified evaluation of f; each D2
point is the exact target terminal's safely decoded local root.
The old D1/up data are reused unchanged. -/
noncomputable def targetMixedPoint
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    Input g.core where
  words := (ForwardQFinalInducedStarredPoint.inducedPoint
    g f fallback σ).words
  upPoint := (ForwardQFinalInducedStarredPoint.inducedPoint
    g f fallback σ).upPoint
  bulletPoint := targetBulletPoint hb g f O L hSupport

/-- Each selected target bullet point belongs to the genuine
support of its own local Ramsey component f_i, using the original
literal R↔D2 correspondence. -/
theorem targetBulletPoint_mem_component_support
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    targetBulletPoint hb g f O L hSupport i ∈
      (f.vector.components i.1).support := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hroot :=
    targetD2LocalPoint_mem_component_support
      hb g f O L hSupport r
  change targetD2LocalPoint hb g f O L hSupport r ∈
    (f.vector.components i.1).support
  rw [← hi]
  exact hroot

/-- The mixed point with EXACT target D2 terminal coordinates
belongs to the REAL mixed-product Ramsey span of f.
No arbitrary D2 supports are guessed and no starred order is
silently imposed. -/
theorem targetMixedPoint_mem_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    targetMixedPoint hb g f O L hSupport fallback σ ∈ f.span := by
  have hBase := ForwardQFinalInducedStarredPoint.inducedPoint_mem_mixed_span
    g f fallback σ
  refine ⟨hBase.1, hBase.2.1, ?_⟩
  intro i
  exact targetBulletPoint_mem_component_support
    hb g f O L hSupport i

/-- At each ORIGINAL literal marker r, the D2 projection from
the assembled local mixed point is the exact corresponding target
terminal in O.tree, not a merely signature-equivalent leaf. -/
theorem targetMixedPoint_markedProjection_eq_targetLeaf
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    (markedProjection g.core
      (targetMixedPoint hb g f O L hSupport fallback σ)
      (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
    (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
      hb g O L
      (targetTree_subset_complete_of_final_support
        g f O hSupport) r).1 := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  have hr : e.symm (ForwardQMarkerCoverage.bulletForMarker g.core r) = r :=
    e.symm_apply_apply r
  change (projected g.core
    ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
      targetBulletPoint hb g f O L hSupport
        (ForwardQMarkerCoverage.bulletForMarker g.core r)⟩).1 = _
  change (projected g.core
    ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
      targetD2LocalPoint hb g f O L hSupport
        (e.symm (ForwardQMarkerCoverage.bulletForMarker g.core r))⟩).1 = _
  rw [hr]
  exact targetD2LocalPoint_projection hb g f O L hSupport r

/-- Corrected IsStarred for the exact chosen target points is
equivalent to the already identified genuine D2 length/order
criterion. In particular, proving this global criterion is the
ONLY additional premise needed to give this mixed span point a
corrected starred certificate. -/
theorem targetMixedPoint_starred_of_bullet_order
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (hOrder : ForwardQIndexedTRanks.BulletLengthsOrdered
      g.core (targetMixedPoint hb g f O L hSupport fallback σ)) :
    ForwardQActualStarredSpace.IsStarred
      g.core (targetMixedPoint hb g f O L hSupport fallback σ) :=
  (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
    g.core (targetMixedPoint hb g f O L hSupport fallback σ)).2 hOrder

end DualTree.ForwardQFinalTargetD2MixedPoint
