import DualTree.Lemma27QBranchDirections

/-!
# Occupied successor directions in the reconstructed Q skeleton

Fix an old interior vertex u. A direction i ∈ Fin b is occupied
when some node in the skeleton lies in the ambient cone u⌢i.

The actual Q tree replaces each literal signature marker s by its
projected node in the designated D₂ cone. Its marker-coordinate map
is bijective onto the bullet indices, and the preceding lemma proves
that this replacement preserves every first-direction relation
from an old base vertex.

We prove equality of the sets of occupied directions in the
literal marker skeleton and in the reconstructed Q skeleton.

This does not by itself show that all b directions are occupied:
that is an additional statement about the original signature.
-/

namespace DualTree.Lemma27QBranchOccupancy

/-- Finite old skeleton before the literal terminal markers are
replaced by their projections. -/
noncomputable def oldSkeleton
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    Finset (Node b) := by
  classical
  exact (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
    (LiteralSignatureR.literalR O cut hout).toFinset

/-- An ambient immediate-successor direction is occupied
by at least one vertex of a finite node set. -/
def Occupied {b : Nat} (S : Finset (Node b))
    (u : Node b) (i : Fin b) : Prop :=
  ∃ t : Node b, t ∈ S ∧ IsPrefix (u ++ [i]) t

/-- The Q reconstruction preserves exactly the occupied
immediate-successor directions at every retained old vertex. -/
theorem occupied_iff_under_Q
    {b n l k m : Nat} {α : Type*}
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
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (u : Node b)
    (hu : u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout)
    (i : Fin b) :
    Occupied
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x) u i ↔
      Occupied (oldSkeleton O cut hout) u i := by
  classical
  let R := LiteralSignatureR.literalR O cut hout
  let M : Type := {s : Node b // s ∈ R}
  let index : M → Fin (LiteralFrontierCount.frontiers T cut).length :=
    LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
  have hsurj : ∀ j : MixedProduct.BulletIndex
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel),
      ∃ s : M, MixedProduct.bulletIndex index s = j := by
    intro j
    exact MixedProduct.bulletIndex_surjective index j
  constructor
  · rintro ⟨v, hv, hdir⟩
    change v ∈ Lemma27SignatureTree.signatureNodes
      T hcomplete cut hcutT hlevel hm
      (Lemma27SignatureTree.oldSignatureBase O cut hout) x at hv
    unfold Lemma27SignatureTree.signatureNodes at hv
    rcases Finset.mem_union.mp hv with hOld | hProj
    · refine ⟨v, ?_, hdir⟩
      change v ∈
        (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
          R.toFinset
      exact Finset.mem_union.mpr (Or.inl hOld)
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hProj
      obtain ⟨s, hjs⟩ := hsurj j
      have hdirP : IsPrefix (u ++ [i])
          (Lemma27SignatureTree.markedProjection
            T hcomplete cut hcutT hlevel hm x j).1 := by
        rw [hj]
        exact hdir
      have hdirS : IsPrefix (u ++ [i]) s.1 := by
        apply (Lemma27QBranchDirections.oldBase_childCone_prefix_iff
          O cut hcut hmax hout T hcomplete hST hcutT hlevel
          hm x u hu s i).1
        rw [hjs]
        exact hdirP
      refine ⟨s.1, ?_, hdirS⟩
      change s.1 ∈
        (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
          R.toFinset
      exact Finset.mem_union.mpr
        (Or.inr (List.mem_toFinset.mpr s.2))
  · rintro ⟨v, hv, hdir⟩
    change v ∈
      (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
      R.toFinset at hv
    rcases Finset.mem_union.mp hv with hOld | hR
    · refine ⟨v, ?_, hdir⟩
      exact Lemma27SignatureTree.signatureNodes_base
        T hcomplete cut hcutT hlevel hm
        (Lemma27SignatureTree.oldSignatureBase O cut hout) x v
        (List.mem_toFinset.mp hOld)
    · let s : M := ⟨v, List.mem_toFinset.mp hR⟩
      let j := MixedProduct.bulletIndex index s
      let t := (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcutT hlevel hm x j).1
      refine ⟨t, ?_, ?_⟩
      · exact Lemma27SignatureTree.signatureNodes_marked
          T hcomplete cut hcutT hlevel hm
          (Lemma27SignatureTree.oldSignatureBase O cut hout) x j
      · exact (Lemma27QBranchDirections.oldBase_childCone_prefix_iff
          O cut hcut hmax hout T hcomplete hST hcutT hlevel
          hm x u hu s i).2 hdir

end DualTree.Lemma27QBranchOccupancy
