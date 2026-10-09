import DualTree.LiteralMarkerCoordinates
import DualTree.MixedProduct

/-!
# Turning distinguished coordinate injections into mixed-product D₂ kinds

The map from the literal signature markers R into the d frontier indices
is injective. Definition 21's mixed-product notation distinguishes the
marked D₂ coordinates from the remaining plain coordinates.

This file builds the corresponding coordinate-kind function from any
injection into Fin d. It proves that the distinguished indices are exactly
the bullet coordinates, that there are no D₁ (up) coordinates, and that
the selected bullet index is bijective with the original markers.

The generic construction is subsequently instantiated with the
source-facing literal marker coordinates. This handles *indexing only*:
the mixed-product word and its colouring transport remain open.
-/

namespace DualTree.MixedProduct

/-- Mark exactly the image of a map into Fin d as D₂/bullet coordinates. -/
noncomputable def bulletKindOfRange
    {d : Nat} {M : Type*} (index : M → Fin d) :
    Fin d → CoordKind := by
  classical
  exact fun i => if ∃ m : M, index m = i then .bullet else .plain

/-- An index is marked precisely when it belongs to the selected range. -/
theorem bulletKindOfRange_iff
    {d : Nat} {M : Type*} (index : M → Fin d)
    (i : Fin d) :
    bulletKindOfRange index i = .bullet ↔
      ∃ m : M, index m = i := by
  classical
  by_cases h : ∃ m : M, index m = i <;>
    simp [bulletKindOfRange, h]

/-- No up-coordinate is introduced by the D₀/D₂ construction. -/
theorem bulletKindOfRange_ne_up
    {d : Nat} {M : Type*} (index : M → Fin d)
    (i : Fin d) :
    bulletKindOfRange index i ≠ .up := by
  classical
  by_cases h : ∃ m : M, index m = i <;>
    simp [bulletKindOfRange, h]

/-- Each distinguished marker has a well-typed bullet-coordinate index. -/
noncomputable def bulletIndex
    {d : Nat} {M : Type*} (index : M → Fin d)
    (m : M) : BulletIndex (bulletKindOfRange index) := by
  classical
  refine ⟨index m, ?_⟩
  exact (bulletKindOfRange_iff index (index m)).2 ⟨m, rfl⟩

/-- Injectivity of the distinguished map is inherited by bullet indexing. -/
theorem bulletIndex_injective
    {d : Nat} {M : Type*} (index : M → Fin d)
    (hinj : Function.Injective index) :
    Function.Injective (bulletIndex index) := by
  intro m n h
  apply hinj
  exact congrArg Subtype.val h

/-- Every selected bullet coordinate has a marker preimage. -/
theorem bulletIndex_surjective
    {d : Nat} {M : Type*} (index : M → Fin d) :
    Function.Surjective (bulletIndex index) := by
  intro i
  obtain ⟨m, hm⟩ :=
    (bulletKindOfRange_iff index i.1).1 i.2
  refine ⟨m, ?_⟩
  exact Subtype.ext hm

/-- The chosen indices identify the marker type bijectively with D₂. -/
theorem bulletIndex_bijective
    {d : Nat} {M : Type*} (index : M → Fin d)
    (hinj : Function.Injective index) :
    Function.Bijective (bulletIndex index) :=
  ⟨bulletIndex_injective index hinj,
    bulletIndex_surjective index⟩

end DualTree.MixedProduct

namespace DualTree.LiteralMarkerProductKind

/-- The actual D₀/D₂ kind of each frontier coordinate in Lemma 27. -/
noncomputable def kind
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind :=
  MixedProduct.bulletKindOfRange
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)

/-- Literal markers are bijective with the resulting bullet coordinates. -/
theorem literalMarker_bullet_bijective
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    Function.Bijective
      (MixedProduct.bulletIndex
        (LiteralMarkerCoordinates.coordinate
          O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :=
  MixedProduct.bulletIndex_bijective
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)
    (LiteralMarkerCoordinates.coordinate_injective
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)

end DualTree.LiteralMarkerProductKind
