import DualTree.ForwardQFinalEnlargedTargetInput
import DualTree.ForwardQFinalTargetTreeEquality

/-!
# A representation-independent Q node-set theorem for target markers

The Q support depends only on its actual D₂ marked projections,
not on how its ordinary coordinate words or alphabet constants
were chosen. The original exact target-tree proof unnecessarily
specialized to one alpha-valued local Ramsey word.

We isolate the generic finite-set fact: any actual corrected Q
input whose projected marked points coincide with the unique
terminals of the target at every ORIGINAL literal source marker
has the same finite node set as the target.

This is valid for any local alphabet, including the genuine
enlarged Corollary-22 alphabet. It uses the target's actual marker
bijection and the source/target equality of old interiors, rather
than equating arbitrary list enumerations.
-/

namespace DualTree.ForwardQFinalGenericTargetNodeSet

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUniqueTargetTerminals

/-- If a source-facing input uses exactly the unique target
terminal at each genuine original literal marker, then every
selected Q projection is an actual vertex of O.tree. -/
theorem markedProjection_mem_target_of_marker_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (x : Input g.core)
    (hmarkers : ∀ r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout,
      (markedProjection g.core x
        (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
      (targetLeafForSourceMarker hb g O L hT r).1)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (markedProjection g.core x i).1 ∈ O.tree := by
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hleaf :
      (targetLeafForSourceMarker hb g O L hT r).1 ∈ O.tree :=
    (targetLeafForSourceMarker hb g O L hT r).2.1
  rw [← hi]
  rw [hmarkers r]
  exact hleaf

/-- Every genuine target terminal occurs as the actual Q
projection of some original source D₂ marker, provided the
entire marked family has the exact marker-to-terminal property.
No list enumeration or guessed D₂ ordering is required. -/
theorem target_terminal_covered_of_marker_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (x : Input g.core)
    (hmarkers : ∀ r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout,
      (markedProjection g.core x
        (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
      (targetLeafForSourceMarker hb g O L hT r).1)
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ i : MixedProduct.BulletIndex (kind g.core),
      (markedProjection g.core x i).1 = t := by
  let d := ForwardQFinalTargetTerminalMarker.targetFrame
    hb g O L hT
  let leaf : ForwardSourceLeafMarkerEquiv.SourceLeaf d :=
    ⟨t, ⟨ht,hterminal⟩⟩
  obtain ⟨rt,hprefix⟩ :=
    ForwardSourceLeafMarkerEquiv.source_leaf_has_marker d leaf
  let r :=
    ForwardQFinalSignatureMarkerTransport.targetMarkerEquiv
      hb g O L rt
  have hroot : r.1 = rt.1 :=
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
    (markedProjection g.core x
      (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
      (targetLeafForSourceMarker hb g O L hT r).1 := hmarkers r
    _ = t := hleaf

/-- The exact generic Q node-set reconstruction: once the
marked projections agree with the target's unique terminals,
the old base interior and ALL target terminals are identical
as finite node SETS. The statement is independent of the
local word's constant alphabet and of the ordinary Q letters. -/
theorem Q_node_set_eq_target_of_marker_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (x : Input g.core)
    (hmarkers : ∀ r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout,
      (markedProjection g.core x
        (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 =
      (targetLeafForSourceMarker hb g O L hT r).1) :
    nodes g.core x = O.tree.toFinset := by
  classical
  ext t
  constructor
  · intro ht
    change t ∈ (ForwardQFixedBase.oldBase g.core).toFinset ∪
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
        markedProjection_mem_target_of_marker_eq
          hb g O L hT x hmarkers i
      rw [heq] at hi
      exact List.mem_toFinset.mpr hi
  · intro ht
    have htO : t ∈ O.tree := List.mem_toFinset.mp ht
    by_cases hinterior : t ∈ SkewTree.interior O.tree
    · have hSource : t ∈ SkewTree.interior g.core.source.tree :=
        (ForwardQFinalLiteralSignatureTree.literal_signature_trees_force_same_interior
          hb g O L t).1 hinterior
      have hOld : t ∈ ForwardQFixedBase.oldBase g.core :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior
          g.core t).2 hSource
      change t ∈ (ForwardQFixedBase.oldBase g.core).toFinset ∪
        (Finset.univ :
          Finset (MixedProduct.BulletIndex (kind g.core))).image
          (fun i => (markedProjection g.core x i).1)
      exact Finset.mem_union.mpr
        (Or.inl (List.mem_toFinset.mpr hOld))
    · obtain ⟨i,hi⟩ :=
        target_terminal_covered_of_marker_eq
          hb g O L hT x hmarkers t htO hinterior
      change t ∈ (ForwardQFixedBase.oldBase g.core).toFinset ∪
        (Finset.univ :
          Finset (MixedProduct.BulletIndex (kind g.core))).image
          (fun i => (markedProjection g.core x i).1)
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))

/-- The new genuine enlarged-alphabet target input has exactly
the requested target's finite Q node set. No global D₂-starred
order or full Q WORD equality is smuggled into this geometric
fact; both remain to be proved independently. -/
theorem coherent_enlarged_target_Q_node_set_eq
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    nodes g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (ForwardQFinalEnlargedTargetInput.coherentTargetInput
          hb g f fallback O cutO H hSupport)) =
      O.tree.toFinset := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  let hT := ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
    g f O hSupport
  apply Q_node_set_eq_target_of_marker_eq
    hb g O L hT
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (ForwardQFinalEnlargedTargetInput.coherentTargetInput
          hb g f fallback O cutO H hSupport))
  intro r
  exact ForwardQFinalEnlargedTargetInput.coherentTargetInput_markedProjection_eq_targetLeaf
    hb g f fallback O cutO H hSupport r

end DualTree.ForwardQFinalGenericTargetNodeSet
