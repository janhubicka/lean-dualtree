import DualTree.ForwardQFinalTargetD2MixedPoint
import DualTree.ForwardQFixedBase
import DualTree.ForwardQFinalLiteralSignatureTree
import DualTree.ForwardQFinalSignatureMarkerTransport
import DualTree.ForwardSourceLeafMarkerEquiv

/-!
# The assembled target D2 mixed point reproduces the target Q tree set

We have chosen, for every source literal R marker, exactly the local
D2 variable-root point whose projection is the UNIQUE corresponding
target O terminal. The source and target corrected signatures have
the same old interior, and the original literal R list matches the
target R list by identical nodes.

This module proves that the actual Q support Finset obtained from
those exact target D2 points equals O.tree.toFinset. The forward
inclusion uses old-interior identity and the marker-to-leaf
projection law. Reverse inclusion uses the target's own verified
leaf/marker correspondence, exact R transport and uniqueness of
the terminal chosen for that original marker.

This equality is deliberately an equality of FINITE NODE SETS, not
equality of arbitrary list enumerations. It does not require an
unproved canonical order on O.tree and does not silently assert the
corrected starred D2 vector-one condition on the assembled tuple.

The remaining proof obligations are to establish that global
corrected starred order for these exact D2 points, combine with the
verified entire-word preimage, and bridge list-independent tree
equality to the appropriate paper notion of starred object equality.
-/

namespace DualTree.ForwardQFinalTargetTreeEquality

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetD2Point
open ForwardQFinalTargetD2MixedPoint
open ForwardQFinalUniqueTargetTerminals

/-- Every D2 projection in the specifically assembled target mixed
point is an ACTUAL terminal of O.tree, by the unique original
R-marker label assigned to that bullet coordinate. -/
theorem targetMixedPoint_markedProjection_mem_target
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
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (markedProjection g.core
      (targetMixedPoint hb g f O L hSupport fallback σ) i).1 ∈
      O.tree := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
    g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hproj :=
    targetMixedPoint_markedProjection_eq_targetLeaf
      hb g f O L hSupport fallback σ r
  have hleaf :
      (targetLeafForSourceMarker hb g O L
        (targetTree_subset_complete_of_final_support
          g f O hSupport) r).1 ∈ O.tree :=
    (targetLeafForSourceMarker hb g O L
      (targetTree_subset_complete_of_final_support
        g f O hSupport) r).2.1
  rw [← hi]
  rw [hproj]
  exact hleaf

/-- Every actual TARGET O terminal occurs among the projections
of the assembled target D2 tuple. The proof uses O's own literal
R marker, carries it back to the ORIGINAL source node, then uses
the previously proved uniqueness of the terminal above that marker. -/
theorem target_terminal_covered_by_markedProjection
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
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ i : MixedProduct.BulletIndex (kind g.core),
      (markedProjection g.core
        (targetMixedPoint hb g f O L hSupport fallback σ) i).1 = t := by
  let hT := targetTree_subset_complete_of_final_support
    g f O hSupport
  let d := ForwardQFinalTargetTerminalMarker.targetFrame
    hb g O L hT
  let leaf : ForwardSourceLeafMarkerEquiv.SourceLeaf d :=
    ⟨t, ⟨ht,hterminal⟩⟩
  obtain ⟨rt,hprefix⟩ :=
    ForwardSourceLeafMarkerEquiv.source_leaf_has_marker d leaf
  let r :=
    ForwardQFinalSignatureMarkerTransport.targetMarkerEquiv
      hb g O L rt
  have hroot :
      r.1 = rt.1 :=
    ForwardQFinalSignatureMarkerTransport.targetMarkerEquiv_root
      hb g O L rt
  have hp : IsPrefix r.1 t := by
    rw [hroot]
    exact hprefix
  have hunique :=
    (Classical.choose_spec
      (unique_target_terminal_for_source_marker
        hb g O L hT r)).2 leaf hp
  have hleaf :
      (targetLeafForSourceMarker hb g O L hT r).1 = t :=
    (congrArg Subtype.val hunique).symm
  refine ⟨ForwardQMarkerCoverage.bulletForMarker g.core r, ?_⟩
  calc
    (markedProjection g.core
        (targetMixedPoint hb g f O L hSupport fallback σ)
        (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
      (targetLeafForSourceMarker hb g O L hT r).1 :=
      targetMixedPoint_markedProjection_eq_targetLeaf
        hb g f O L hSupport fallback σ r
    _ = t := hleaf

/-- The ACTUAL Q vertex SET formed from the exact target D2 points
is EQUAL to the requested starred O.tree node set. This includes
the old interior and EVERY requested terminal, without relying on
a canonical order of either finite list. -/
theorem targetMixedPoint_Q_node_set_eq_target
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
    nodes g.core (targetMixedPoint hb g f O L hSupport fallback σ) =
      O.tree.toFinset := by
  classical
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  ext t
  constructor
  · intro ht
    change t ∈ (oldBase g.core).toFinset ∪
      (Finset.univ :
        Finset (MixedProduct.BulletIndex (kind g.core))).image
        (fun i => (markedProjection g.core x i).1) at ht
    rcases Finset.mem_union.mp ht with hold | hmark
    · have hSource : t ∈ SkewTree.interior g.core.source.tree :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior
          g.core t).1 (List.mem_toFinset.mp hold)
      have hTarget : t ∈ SkewTree.interior O.tree :=
        (ForwardQFinalLiteralSignatureTree.literal_signature_trees_force_same_interior
          hb g O L t).2 hSource
      exact List.mem_toFinset.mpr (List.mem_filter.mp hTarget).1
    · obtain ⟨i,_,heq⟩ := Finset.mem_image.mp hmark
      have hi : (markedProjection g.core x i).1 ∈ O.tree :=
        targetMixedPoint_markedProjection_mem_target
          hb g f O L hSupport fallback σ i
      rw [heq] at hi
      exact List.mem_toFinset.mpr hi
  · intro ht
    have htO : t ∈ O.tree := List.mem_toFinset.mp ht
    by_cases hinterior : t ∈ SkewTree.interior O.tree
    · have hSource : t ∈ SkewTree.interior g.core.source.tree :=
        (ForwardQFinalLiteralSignatureTree.literal_signature_trees_force_same_interior
          hb g O L t).1 hinterior
      have hOld : t ∈ oldBase g.core :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior
          g.core t).2 hSource
      change t ∈ (oldBase g.core).toFinset ∪
        (Finset.univ :
          Finset (MixedProduct.BulletIndex (kind g.core))).image
          (fun i => (markedProjection g.core x i).1)
      exact Finset.mem_union.mpr
        (Or.inl (List.mem_toFinset.mpr hOld))
    · obtain ⟨i,hi⟩ :=
        target_terminal_covered_by_markedProjection
          hb g f O L hSupport fallback σ t htO hinterior
      change t ∈ (oldBase g.core).toFinset ∪
        (Finset.univ :
          Finset (MixedProduct.BulletIndex (kind g.core))).image
          (fun i => (markedProjection g.core x i).1)
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))

end DualTree.ForwardQFinalTargetTreeEquality
