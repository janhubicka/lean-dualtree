import DualTree.ForwardSemiCompleteInitial
import DualTree.ForwardSourceBoundaryEquiv

/-!
# Canonical Definition-24 boundary for arbitrary semi-complete starred trees

For every eligible forward-order starred tree U, the intrinsic directional
walk maps the first-l model boundary bijectively onto the actual leaves.
The exceptional A_0 = {[]} maps to the sole leaf, the root. All model
addresses used here are admissible, so no totalization fallback is used.

The map has its true support root and immediate directional successor
laws, preserves and reflects forward order, and its boundary addresses
fit in the original ambient height. No Q frame, enclosing complete tree,
selector agreement, or separately assumed model admissibility is needed.
This supplies the missing arbitrary-U semantics of the corrected selector.
-/

namespace DualTree.ForwardSemiCompleteBoundary

open ForwardModelBoundaryHeap
open ForwardCanonicalPartialWalkUniqueness
open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteAddresses
open ForwardSemiCompleteAddressOrder
open ForwardSemiCompleteInitial

variable {b n l : Nat} {α : Type*}

/-- The full Definition-24 boundary, including its exceptional zero case. -/
abbrev Boundary (b l : Nat) := {a : Node b // Definition24Boundary l a}

/-- Actual leaves of U, with membership and terminality both retained. -/
abbrev Leaf
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :=
  {t : Node b // t ∈ U.tree ∧ t ∉ SkewTree.interior U.tree}

/-- Every model boundary address follows genuine unique support successors. -/
theorem boundary_admissible
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Boundary b l) :
    CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a.1 := by
  by_cases hzero : l = 0
  · have ha : a.1 = [] := by
      simpa [Definition24Boundary, hzero] using a.2
    simp [ha, CanonicalSupportWalk.Admissible]
  · have ha : ModelBoundary l a.1 := by
      simpa [Definition24Boundary, hzero] using a.2
    obtain ⟨p, i, hp, hrepr⟩ := ha.2
    have hpValid := modelInterior_admissible hb U p hp
    have hpInterior := canonicalWalkAll_interior hb U p hp
    have hbranch := full_directions U (canonicalWalkAll U p) hpInterior i
    rw [hrepr]
    exact (ForwardSourceBoundaryLeaves.admissible_append_singleton_iff
      U.tree (starredRootAll U) p i).2 ⟨hpValid, hbranch⟩

/-- Boundary addresses land at genuine leaves, rather than at a fallback vertex. -/
theorem boundary_is_leaf
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Boundary b l) :
    canonicalWalkAll U a.1 ∈ U.tree ∧
      canonicalWalkAll U a.1 ∉ SkewTree.interior U.tree := by
  refine ⟨CanonicalSupportWalk.walk_mem_of_admissible
    U.tree (starredRootAll U) a.1 (starredRootAll_mem U)
    (boundary_admissible hb U a), ?_⟩
  intro hint
  have hmodel : ModelInterior l a.1 :=
    (modelInterior_iff_interior_address hb U a.1).2
      ⟨⟨a.1, boundary_admissible hb U a⟩, rfl, hint⟩
  by_cases hzero : l = 0
  · simpa [ModelInterior, hzero] using hmodel
  · have ha : ModelBoundary l a.1 := by
      simpa [Definition24Boundary, hzero] using a.2
    exact ha.1 hmodel

/-- Conversely the address of every genuine leaf belongs to A_l. -/
theorem leaf_address_boundary
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (u : Address U)
    (hLeaf : (realize U u).1 ∉ SkewTree.interior U.tree) :
    Definition24Boundary l u.1 := by
  cases hrev : u.1.reverse with
  | nil =>
      have ha : u.1 = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hzero : l = 0 := by
        by_contra hne
        have hmodel : ModelInterior l u.1 := by
          simpa [ModelInterior, heapIndex, ha] using Nat.pos_of_ne_zero hne
        exact hLeaf (canonicalWalkAll_interior hb U u.1 hmodel)
      simp [Definition24Boundary, hzero, ha]
  | cons i revParent =>
      let p : Node b := revParent.reverse
      have hrepr : u.1 = p ++ [i] := by
        have h := congrArg List.reverse hrev
        simpa [p] using h
      have hvalid : CanonicalSupportWalk.Admissible U.tree
          (starredRootAll U) (p ++ [i]) := by
        simpa only [hrepr] using u.2
      have hsplit := (ForwardSourceBoundaryLeaves.admissible_append_singleton_iff
        U.tree (starredRootAll U) p i).1 hvalid
      let parent : Address U := ⟨p, hsplit.1⟩
      let child : Address U := ⟨p ++ [i], hvalid⟩
      have hstrict : IsStrictPrefix (realize U parent).1 (realize U child).1 :=
        ForwardSourceBoundaryEquiv.admissible_last_strictPrefix
          U.tree (starredRootAll U) p i hvalid
      have hpInterior : (realize U parent).1 ∈ SkewTree.interior U.tree :=
        SignatureInteriorPersistence.interior_of_strict_descendant
          U.tree (realize U parent).1 (realize U child).1
          (realize U parent).2 (realize U child).2 hstrict
      have hpModel : ModelInterior l p :=
        (modelInterior_iff_interior_address hb U p).2
          ⟨parent, rfl, hpInterior⟩
      have hout : ¬ ModelInterior l u.1 := by
        intro hmodel
        exact hLeaf (canonicalWalkAll_interior hb U u.1 hmodel)
      have hzero : l ≠ 0 := by
        intro hz
        simpa [ModelInterior, hz] using hpModel
      exact (definition24Boundary_pos_iff (Nat.pos_of_ne_zero hzero) u.1).2
        ⟨hout, p, i, hpModel, hrepr⟩

/-- The selector on boundary addresses, valued in actual leaves. -/
noncomputable def boundaryRealize
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Boundary b l → Leaf U :=
  fun a => ⟨canonicalWalkAll U a.1, boundary_is_leaf hb U a⟩

theorem boundaryRealize_injective
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Function.Injective (boundaryRealize hb U) := by
  intro a d had
  apply Subtype.ext
  exact CanonicalSupportInjective.walk_injective_of_admissible
    U.tree a.1 (starredRootAll U) d.1
    (boundary_admissible hb U a) (boundary_admissible hb U d)
    (congrArg Subtype.val had)

theorem boundaryRealize_surjective
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Function.Surjective (boundaryRealize hb U) := by
  intro t
  obtain ⟨a, hadm, hwalk, _⟩ := has_address U t.1 t.2.1
  let u : Address U := ⟨a, hadm⟩
  have hLeaf : (realize U u).1 ∉ SkewTree.interior U.tree := by
    change canonicalWalkAll U a ∉ _
    rw [hwalk]
    exact t.2.2
  refine ⟨⟨a, leaf_address_boundary hb U u hLeaf⟩, ?_⟩
  exact Subtype.ext hwalk

/-- Canonical leaf bijection for every eligible U and every l, including zero. -/
noncomputable def boundaryLeafEquiv
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Boundary b l ≃ Leaf U :=
  Equiv.ofBijective (boundaryRealize hb U)
    ⟨boundaryRealize_injective hb U, boundaryRealize_surjective hb U⟩

/-- The canonical map has the root of U itself. -/
theorem canonicalWalkAll_root
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    canonicalWalkAll U [] = starredRootAll U := rfl

/-- At each model interior, a child is a real immediate support successor
in its prescribed ambient direction. No branch-existence premise remains. -/
theorem canonicalWalkAll_child
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (p : Node b) (i : Fin b)
    (hp : ModelInterior l p) :
    SkewTree.immediateSuccB U.tree (canonicalWalkAll U p)
      (canonicalWalkAll U (p ++ [i])) = true ∧
    IsPrefix (canonicalWalkAll U p ++ [i])
      (canonicalWalkAll U (p ++ [i])) := by
  have hbranch := full_directions U (canonicalWalkAll U p)
    (canonicalWalkAll_interior hb U p hp) i
  have h := CanonicalSupportWalk.next_unique U.tree
    (canonicalWalkAll U p) i hbranch
  simpa only [canonicalWalkAll, CanonicalSupportWalk.walk_append,
    CanonicalSupportWalk.walk] using h

/-- The boundary's own addresses fit inside the ambient homogeneous tree. -/
theorem boundary_bounded
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Boundary b l) :
    InHomTree n a.1 :=
  admissible_address_bounded U a.1 (boundary_admissible hb U a)

/-- The boundary selector preserves and reflects the corrected auxiliary order. -/
theorem boundary_forwardAux_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a d : Boundary b l) :
    ForwardAux a.1 d.1 ↔
      ForwardAux (canonicalWalkAll U a.1) (canonicalWalkAll U d.1) :=
  forwardAux_realize_iff U
    ⟨a.1, boundary_admissible hb U a⟩
    ⟨d.1, boundary_admissible hb U d⟩

/-- At l=0 the boundary is the singleton root and that root is a genuine leaf. -/
theorem zero_root_is_leaf
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n 0 α
      (SkewTree.forwardAuxB (b := b))) :
    starredRootAll U ∈ U.tree ∧
      starredRootAll U ∉ SkewTree.interior U.tree :=
  boundary_is_leaf hb U ⟨[], by simp [Definition24Boundary]⟩

end DualTree.ForwardSemiCompleteBoundary
