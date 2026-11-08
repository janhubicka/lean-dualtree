import DualTree.UpLeafGeometry
import DualTree.VectorSkew

/-!
# Track C: genuine intrinsic-height-two complete-skew geometry

A height-two support is not two unrelated singleton supports. Its root has
one immediate support successor in each of the b distinct ambient directions,
with all successors at the same larger ambient level.

We reuse the *proved* skew and branch calculations from UpLeafGeometry and
upgrade those supports to genuine k=2 completeness, for both the paper's
auxiliary order and the forward-order repair. Equal support in every vector
coordinate then satisfies both cross-coordinate ordering conditions.

This file asserts only geometric results. Flat Hales--Jewett selection, legal
tree variable words and the all-D0 Ramsey theorem are separate interfaces.
-/

namespace DualTree.HigherSkewGeometry

open DualTree
open DualTree.UpLeafGeometry

/-- One root and b genuine nodes in different branches at the same level
form a 2-complete skew support once skewness is known. No fixed-root
Hales--Jewett assumption is made. -/
theorem star_complete_two_of_skew
    {b n : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Node b) (leaf : Fin b → Node b)
    (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    (hskew : SkewTree.skewB aux (star r leaf) = true) :
    SkewTree.completeB aux 2 (star r leaf) = true := by
  have hrest : (star r leaf).all (fun s =>
      let deg := (SkewTree.immediateSuccs (star r leaf) s).length
      if deg = 0 then
        decide (SkewTree.heightAt (star r leaf) s + 1 = 2)
      else
        decide (deg = b)) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    rcases (mem_star_iff r leaf s).mp hs with hroot | ⟨i, rfl⟩
    · rw [hroot]
      have hsucc := star_root_successors r leaf hr hlen hbranch
      simp [hsucc, Nat.ne_of_gt hb]
    · have hsucc := star_leaf_successors r leaf hr hlen i
      have hheight := star_height_leaf r leaf hr hlen hbranch i
      simp [hsucc, hheight]
  simpa [SkewTree.completeB, hskew] using hrest

/-- At a star's support node, the intrinsic height and ambient length are
exactly those of either the root or a level-n leaf. -/
theorem star_root_or_leaf_level
    {b n : Nat}
    (r : Node b) (leaf : Fin b → Node b)
    (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    (s : Node b) (hs : s ∈ star r leaf) :
    (SkewTree.heightAt (star r leaf) s = 0 ∧ s.length = r.length) ∨
      (SkewTree.heightAt (star r leaf) s = 1 ∧ s.length = n) := by
  rcases (mem_star_iff r leaf s).mp hs with hroot | ⟨i, rfl⟩
  · rw [hroot]
    exact Or.inl ⟨star_height_root r leaf hr hlen, rfl⟩
  · exact Or.inr ⟨star_height_leaf r leaf hr hlen hbranch i, hlen i⟩

/-- Any support with length determined by intrinsic level, and strictly
increasing from one level to the next, is a vector-complete support when
repeated identically across all coordinates. The two vector clauses are
proved, not declared vacuous. -/
theorem identical_vector_complete
    {b d k : Nat}
    (aux : Node b → Node b → Bool)
    (S : List (Node b))
    (hcomplete : SkewTree.completeB aux k S = true)
    (hsame : ∀ s ∈ S, ∀ t ∈ S,
      SkewTree.heightAt S s = SkewTree.heightAt S t →
      s.length = t.length)
    (hstrict : ∀ s ∈ S, ∀ t ∈ S,
      SkewTree.heightAt S s < SkewTree.heightAt S t →
      s.length < t.length) :
    VectorSkew.vectorCompleteB aux k
      (fun _ : Fin d => S) = true := by
  have hmember {m : Nat} {s : Node b}
      (hs : s ∈ VectorSkew.levelNodes S m) :
      s ∈ S ∧ SkewTree.heightAt S s = m := by
    simpa [VectorSkew.levelNodes] using hs
  have hc : (SkewTree.allFin d).all
      (fun _ => SkewTree.completeB aux k S) = true := by
    apply List.all_eq_true.mpr
    intro _ _
    exact hcomplete
  have hs : VectorSkew.sameLevelOrderedB
      (fun _ : Fin d => S) k = true := by
    unfold VectorSkew.sameLevelOrderedB
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    by_cases hij : i < j
    · simp only [if_pos hij]
      apply List.all_eq_true.mpr
      intro m _
      apply List.all_eq_true.mpr
      intro s hs
      apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨hsS, hsm⟩ := hmember hs
      obtain ⟨htS, htm⟩ := hmember ht
      have hlen : s.length ≤ t.length :=
        Nat.le_of_eq (hsame s hsS t htS (hsm.trans htm.symm))
      simp [hlen]
    · simp [hij]
  have ht : VectorSkew.successiveLevelsSeparatedB
      (fun _ : Fin d => S) k = true := by
    unfold VectorSkew.successiveLevelsSeparatedB
    apply List.all_eq_true.mpr
    intro m _
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    apply List.all_eq_true.mpr
    intro s hs
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨hsS, hsm⟩ := hmember hs
    obtain ⟨htS, htm⟩ := hmember ht
    have hlt : SkewTree.heightAt S s < SkewTree.heightAt S t := by
      omega
    have hlen : s.length < t.length :=
      hstrict s hsS t htS hlt
    simp [hlen]
  simp [VectorSkew.vectorCompleteB, hc, hs, ht]

/-- A genuine 2-complete skew star repeated in every coordinate satisfies
the full vector 2-complete-skew definition. -/
theorem star_vector_complete_two_of_skew
    {b n d : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Node b) (leaf : Fin b → Node b)
    (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    (hskew : SkewTree.skewB aux (star r leaf) = true) :
    VectorSkew.vectorCompleteB aux 2
      (fun _ : Fin d => star r leaf) = true := by
  apply identical_vector_complete aux (star r leaf)
    (star_complete_two_of_skew hb aux r leaf hr hlen hbranch hskew)
  · intro s hs t ht heq
    rcases star_root_or_leaf_level r leaf hr hlen hbranch s hs with hsr | hsl
    · rcases star_root_or_leaf_level r leaf hr hlen hbranch t ht with htr | htl
      · omega
      · omega
    · rcases star_root_or_leaf_level r leaf hr hlen hbranch t ht with htr | htl
      · omega
      · omega
  · intro s hs t ht hlt
    rcases star_root_or_leaf_level r leaf hr hlen hbranch s hs with hsr | hsl
    · rcases star_root_or_leaf_level r leaf hr hlen hbranch t ht with htr | htl
      · omega
      · omega
    · rcases star_root_or_leaf_level r leaf hr hlen hbranch t ht with htr | htl
      · omega
      · omega

/-- The actual b-branching star at ambient depth n: root r and one
length-n extension in each outgoing direction. The support is suitable
for a tree word of ambient height n+1. -/
def ambientStar
    {b n : Nat} (hb : 0 < b) (r : BoundedNode b n) :
    List (Node b) :=
  star r.1 (fun i => (ambientLeaf hb r i).1)

theorem ambientStar_complete_forward
    {b n : Nat} (hb : 0 < b) (r : BoundedNode b n) :
    SkewTree.completeB SkewTree.forwardAuxB 2 (ambientStar hb r) = true := by
  have hskew : SkewTree.skewB SkewTree.forwardAuxB (ambientStar hb r) = true := by
    simpa [ambientStar, UpLeafGeometry.star, UpLeafGeometry.ambientLeaves,
      List.map_ofFn, Function.comp_def] using extended_support_skew_forward hb r
  exact star_complete_two_of_skew hb SkewTree.forwardAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) hskew

theorem ambientStar_complete_paper
    {b n : Nat} (hb : 0 < b) (r : BoundedNode b n) :
    SkewTree.completeB SkewTree.paperAuxB 2 (ambientStar hb r) = true := by
  have hskew : SkewTree.skewB SkewTree.paperAuxB (ambientStar hb r) = true := by
    simpa [ambientStar, UpLeafGeometry.star, UpLeafGeometry.ambientLeaves,
      List.map_ofFn, Function.comp_def] using extended_support_skew_paper hb r
  exact star_complete_two_of_skew hb SkewTree.paperAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) hskew

theorem ambientStar_vector_complete_forward
    {b n d : Nat} (hb : 0 < b) (r : BoundedNode b n) :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 2
      (fun _ : Fin d => ambientStar hb r) = true := by
  have hskew : SkewTree.skewB SkewTree.forwardAuxB (ambientStar hb r) = true := by
    simpa [ambientStar, UpLeafGeometry.star, UpLeafGeometry.ambientLeaves,
      List.map_ofFn, Function.comp_def] using extended_support_skew_forward hb r
  exact star_vector_complete_two_of_skew hb SkewTree.forwardAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) hskew

theorem ambientStar_vector_complete_paper
    {b n d : Nat} (hb : 0 < b) (r : BoundedNode b n) :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 2
      (fun _ : Fin d => ambientStar hb r) = true := by
  have hskew : SkewTree.skewB SkewTree.paperAuxB (ambientStar hb r) = true := by
    simpa [ambientStar, UpLeafGeometry.star, UpLeafGeometry.ambientLeaves,
      List.map_ofFn, Function.comp_def] using extended_support_skew_paper hb r
  exact star_vector_complete_two_of_skew hb SkewTree.paperAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) hskew

end DualTree.HigherSkewGeometry
