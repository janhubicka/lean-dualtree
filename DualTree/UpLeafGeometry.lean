import DualTree.MixedProduct
import DualTree.SkewBranchGeometry

/-!
# Genuine ambient leaves above a height-one support

For a root `r` below ambient level `n`, choose one level-`n` extension
of each immediate ambient direction `r ++ [i]`.  The resulting `b`
leaves are distinct, and adjoining them to `[r]` gives a skew tree.
The proof works for both auxiliary orders: their tie-breaks play no
role because all new leaves have the same ambient length.

The abstract construction allows arbitrary tails in the separate
directions.  The concrete construction pads each direction by zeroes
and needs exactly the source bound `r.length < n` and `0 < b`.
These are real `LeafNode b n` values, not placeholders in an empty
index type.  Mixed-word and coloring consequences are separate.
-/

namespace DualTree.UpLeafGeometry

/-- A root followed by one selected node in each ambient direction. -/
def star {b : Nat} (r : Node b) (leaf : Fin b → Node b) : List (Node b) :=
  r :: List.ofFn leaf

theorem mem_star_iff {b : Nat} (r : Node b) (leaf : Fin b → Node b)
    (s : Node b) :
    s ∈ star r leaf ↔ s = r ∨ ∃ i, leaf i = s := by
  simp [star, List.mem_ofFn]

/-- The first direction is determined by any node extending it. -/
theorem direction_eq_of_prefix {b : Nat} (r : Node b)
    (leaf : Fin b → Node b)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    {i j : Fin b} (h : IsPrefix (r ++ [i]) (leaf j)) : i = j := by
  have hp : IsPrefix (r ++ [i]) (r ++ [j]) :=
    CutFrontier.prefix_of_prefix_length_le h (hbranch j) (by simp)
  have heq := CutPreservation.prefix_eq_of_length_eq hp (by simp)
  simpa using heq

theorem leaf_injective {b : Nat} (r : Node b)
    (leaf : Fin b → Node b)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) :
    Function.Injective leaf := by
  intro i j hij
  apply direction_eq_of_prefix r leaf hbranch
  rw [← hij]
  exact hbranch i

theorem root_prefix_leaf {b : Nat} (r : Node b)
    (leaf : Fin b → Node b)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) (i : Fin b) :
    IsPrefix r (leaf i) :=
  isPrefix_trans ⟨[i], rfl⟩ (hbranch i)

private theorem strictPrefixB_false_of_length_le {b : Nat}
    {s t : Node b} (hlen : t.length ≤ s.length) :
    SkewTree.strictPrefixB s t = false := by
  cases h : SkewTree.strictPrefixB s t with
  | false => rfl
  | true =>
      have hp := (SkewBranchGeometry.strictPrefixB_iff s t).mp h
      exact (hp.2 (CutPreservation.prefix_eq_of_length_eq hp.1
        (Nat.le_antisymm (prefix_length_le hp.1) hlen))).elim

private theorem root_strict_leaf {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) (i : Fin b) :
    SkewTree.strictPrefixB r (leaf i) = true := by
  apply (SkewBranchGeometry.strictPrefixB_iff r (leaf i)).mpr
  refine ⟨root_prefix_leaf r leaf hbranch i, ?_⟩
  intro heq
  have := congrArg List.length heq
  rw [hlen i] at this
  omega

theorem star_nodup {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) :
    (star r leaf).Nodup := by
  have hnot : r ∉ List.ofFn leaf := by
    intro h
    rcases List.mem_ofFn.mp h with ⟨i, hi⟩
    have := congrArg List.length hi
    rw [hlen i] at this
    omega
  exact List.nodup_cons.mpr
    ⟨hnot, List.nodup_ofFn.mpr (leaf_injective r leaf hbranch)⟩

theorem star_height_root {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n) :
    SkewTree.heightAt (star r leaf) r = 0 := by
  have hempty : (List.ofFn leaf).filter
      (fun s => SkewTree.strictPrefixB s r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    rcases List.mem_ofFn.mp hs with ⟨i, rfl⟩
    have hfalse : SkewTree.strictPrefixB (leaf i) r = false :=
      strictPrefixB_false_of_length_le (by rw [hlen i]; omega)
    simp [hfalse]
  have hself : SkewTree.strictPrefixB r r = false := by
    simp [SkewTree.strictPrefixB]
  change ((r :: List.ofFn leaf).filter
    (fun s => SkewTree.strictPrefixB s r)).length = 0
  simp [hself, hempty]

theorem star_height_leaf {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) (i : Fin b) :
    SkewTree.heightAt (star r leaf) (leaf i) = 1 := by
  have hempty : (List.ofFn leaf).filter
      (fun s => SkewTree.strictPrefixB s (leaf i)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    rcases List.mem_ofFn.mp hs with ⟨j, rfl⟩
    have hfalse : SkewTree.strictPrefixB (leaf j) (leaf i) = false :=
      strictPrefixB_false_of_length_le (by rw [hlen i, hlen j])
    simp [hfalse]
  have hroot := root_strict_leaf r leaf hr hlen hbranch i
  change ((r :: List.ofFn leaf).filter
    (fun s => SkewTree.strictPrefixB s (leaf i))).length = 1
  simp [hroot, hempty]

theorem star_immediate_root_leaf {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) (i : Fin b) :
    SkewTree.immediateSuccB (star r leaf) r (leaf i) = true := by
  apply (SkewBranchGeometry.immediateSuccB_iff (star r leaf) r (leaf i)).mpr
  refine ⟨by simp [star, List.mem_ofFn],
    (SkewBranchGeometry.strictPrefixB_iff r (leaf i)).mp
      (root_strict_leaf r leaf hr hlen hbranch i), ?_⟩
  intro s hs ⟨hrs, hsi⟩
  rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨j, rfl⟩
  · exact hrs.2 rfl
  · exact hsi.2 (CutPreservation.prefix_eq_of_length_eq hsi.1
      ((hlen j).trans (hlen i).symm))

theorem star_root_successors {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) :
    SkewTree.immediateSuccs (star r leaf) r = List.ofFn leaf := by
  have hself : SkewTree.immediateSuccB (star r leaf) r r = false := by
    simp [SkewTree.immediateSuccB, SkewTree.strictPrefixB]
  have hfilter : (List.ofFn leaf).filter
      (fun s => SkewTree.immediateSuccB (star r leaf) r s) =
      List.ofFn leaf := by
    apply List.filter_eq_self.mpr
    intro s hs
    rcases List.mem_ofFn.mp hs with ⟨i, rfl⟩
    exact star_immediate_root_leaf r leaf hr hlen hbranch i
  change (r :: List.ofFn leaf).filter
    (fun s => SkewTree.immediateSuccB (star r leaf) r s) = List.ofFn leaf
  simpa [hself] using hfilter

theorem star_leaf_successors {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n) (i : Fin b) :
    SkewTree.immediateSuccs (star r leaf) (leaf i) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro s hs
  have hbound : s.length ≤ (leaf i).length := by
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨j, rfl⟩
    · rw [hlen i]
      omega
    · rw [hlen i, hlen j]
  have hfalse := strictPrefixB_false_of_length_le hbound
  simp [SkewTree.immediateSuccB, hfalse]

private theorem singleton_of_nodup_unique_mem {α : Type*}
    (L : List α) (a : α) (hn : L.Nodup)
    (ha : a ∈ L) (hu : ∀ x, x ∈ L → x = a) : L = [a] := by
  cases L with
  | nil => simp at ha
  | cons x xs =>
      have hx : x = a := hu x (by simp)
      subst x
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hy : y = a := hu y (by simp)
          have hnot := (List.nodup_cons.mp hn).1
          exact (hnot (by simp [hy])).elim

theorem star_branchWitnesses {b n : Nat} (r : Node b)
    (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i)) (i : Fin b) :
    SkewTree.branchWitnesses (star r leaf) r i = [leaf i] := by
  apply singleton_of_nodup_unique_mem
  · exact (star_nodup r leaf hr hlen hbranch).filter _
  · apply (SkewBranchGeometry.mem_branchWitnesses_iff
      (star r leaf) r (leaf i) i).mpr
    exact ⟨star_immediate_root_leaf r leaf hr hlen hbranch i, hbranch i⟩
  · intro s hs
    have hparts := (SkewBranchGeometry.mem_branchWitnesses_iff
      (star r leaf) r s i).mp hs
    have hsucc := (SkewBranchGeometry.immediateSuccB_iff
      (star r leaf) r s).mp hparts.1
    rcases (mem_star_iff r leaf s).mp hsucc.1 with rfl | ⟨j, rfl⟩
    · exact (hsucc.2.1.2 rfl).elim
    · have hij : i = j := direction_eq_of_prefix r leaf hbranch hparts.2
      rw [hij]

/-- The full skew certificate for any actual level-`n` branch representatives.
Only the absence of a leaf before the root is required of the auxiliary order. -/
theorem star_skew {b n : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Node b) (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    (haux : ∀ i, aux (leaf i) r = false) :
    SkewTree.skewB aux (star r leaf) = true := by
  have hnodup := star_nodup r leaf hr hlen hbranch
  have hrooted : SkewTree.rootedB (star r leaf) = true := by
    apply List.any_eq_true.mpr
    refine ⟨r, by simp [star], ?_⟩
    apply List.all_eq_true.mpr
    intro s hs
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨i, rfl⟩
    · simp
    · exact SkewBranchGeometry.isPrefixOf_true_of_prefix
        (root_prefix_leaf r leaf hbranch i)
  have hzero := star_height_root r leaf hr hlen
  have hone := star_height_leaf r leaf hr hlen hbranch
  have hII : SkewTree.condIIB (star r leaf) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    apply List.all_eq_true.mpr
    intro t ht
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨i, rfl⟩ <;>
      rcases (mem_star_iff r leaf t).mp ht with rfl | ⟨j, rfl⟩ <;>
      simp [hzero, hone, hlen]
  have hIII : SkewTree.condIIIB (star r leaf) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    apply List.all_eq_true.mpr
    intro t ht
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨i, rfl⟩ <;>
      rcases (mem_star_iff r leaf t).mp ht with rfl | ⟨j, rfl⟩ <;>
      simp [hzero, hone, hlen, hr]
  have hfull : SkewTree.fullBeforeB aux (star r leaf) r = true := by
    apply List.all_eq_true.mpr
    intro s hs
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨i, rfl⟩
    · simp
    · simp [haux i]
  have hempty : SkewTree.emptyAfterB aux (star r leaf) r = true := by
    apply List.all_eq_true.mpr
    intro s hs
    rcases (mem_star_iff r leaf s).mp hs with rfl | ⟨i, rfl⟩
    · simp
    · simp [star_leaf_successors r leaf hr hlen i]
  have hcount : (SkewTree.immediateSuccs (star r leaf) r).length = b := by
    rw [star_root_successors r leaf hr hlen hbranch]
    simp
  have hbranches : ∀ i : Fin b,
      SkewTree.uniqueBranchB (star r leaf) r i = true := by
    intro i
    simp [SkewTree.uniqueBranchB, star_branchWitnesses r leaf hr hlen hbranch i]
  have hIV : SkewTree.condIVB aux (star r leaf) = true := by
    let iLast : Fin b := ⟨b - 1, by omega⟩
    have hlast : iLast.val + 1 = b := by
      dsimp [iLast]
      omega
    have hpartial : SkewTree.partialAtB (star r leaf) r iLast = true := by
      simp only [SkewTree.partialAtB, Bool.and_eq_true]
      constructor
      · simp [hcount, hlast]
      · apply List.all_eq_true.mpr
        intro i _
        exact hbranches i
    apply List.any_eq_true.mpr
    refine ⟨r, by simp [star], ?_⟩
    apply List.any_eq_true.mpr
    refine ⟨iLast, DirectionalSupport.mem_allFin b iLast, ?_⟩
    simp [hfull, hempty, hpartial]
  simp [SkewTree.skewB, hnodup, hrooted, hII, hIII, hIV]

/-- Choose a real ambient-level leaf by taking a requested outgoing direction
and filling the remaining positions with zeroes. -/
def ambientLeaf {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (i : Fin b) : MixedProduct.LeafNode b n :=
  ⟨r.1 ++ [i] ++ List.replicate (n - (r.1.length + 1)) ⟨0, hb⟩, by
    have hr := r.2
    simp only [List.length_append, List.length_singleton, List.length_replicate]
    omega⟩

/-- The selected leaf list contains exactly one ambient-level leaf per direction. -/
def ambientLeaves {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : List (MixedProduct.LeafNode b n) :=
  List.ofFn (ambientLeaf hb r)

theorem direction_prefix_ambientLeaf {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (i : Fin b) :
    IsPrefix (r.1 ++ [i]) (ambientLeaf hb r i).1 :=
  ⟨List.replicate (n - (r.1.length + 1)) ⟨0, hb⟩, rfl⟩

theorem prefix_ambientLeaf {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (i : Fin b) :
    IsPrefix r.1 (ambientLeaf hb r i).1 :=
  isPrefix_trans ⟨[i], rfl⟩ (direction_prefix_ambientLeaf hb r i)

theorem ambientLeaf_val_injective {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) :
    Function.Injective (fun i => (ambientLeaf hb r i).1) :=
  leaf_injective r.1 (fun i => (ambientLeaf hb r i).1)
    (direction_prefix_ambientLeaf hb r)

theorem ambientLeaf_injective {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : Function.Injective (ambientLeaf hb r) := by
  intro i j hij
  exact ambientLeaf_val_injective hb r (congrArg Subtype.val hij)

theorem ambientLeaves_nodup {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : (ambientLeaves hb r).Nodup :=
  List.nodup_ofFn.mpr (ambientLeaf_injective hb r)

theorem ambientLeaves_length {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : (ambientLeaves hb r).length = b := by
  simp [ambientLeaves]

theorem mem_ambientLeaves_iff {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (x : MixedProduct.LeafNode b n) :
    x ∈ ambientLeaves hb r ↔ ∃ i, ambientLeaf hb r i = x := by
  simp [ambientLeaves, List.mem_ofFn]

theorem ambientLeaf_mem {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (i : Fin b) :
    ambientLeaf hb r i ∈ ambientLeaves hb r :=
  (mem_ambientLeaves_iff hb r _).mpr ⟨i, rfl⟩

theorem extended_support_skew_paper {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) :
    SkewTree.skewB SkewTree.paperAuxB
      ([r.1] ++ (ambientLeaves hb r).map Subtype.val) = true := by
  have haux : ∀ i : Fin b,
      SkewTree.paperAuxB (ambientLeaf hb r i).1 r.1 = false := by
    intro i
    have hr := r.2
    have hlen := (ambientLeaf hb r i).2
    simp only [SkewTree.paperAuxB, PaperAux, hlen]
    have hnlt : ¬ n < r.1.length := by omega
    have hne : n ≠ r.1.length := by omega
    simp [hnlt, hne]
  have h := star_skew hb SkewTree.paperAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) haux
  simpa [star, ambientLeaves, List.map_ofFn] using h

theorem extended_support_skew_forward {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) :
    SkewTree.skewB SkewTree.forwardAuxB
      ([r.1] ++ (ambientLeaves hb r).map Subtype.val) = true := by
  have haux : ∀ i : Fin b,
      SkewTree.forwardAuxB (ambientLeaf hb r i).1 r.1 = false := by
    intro i
    have hr := r.2
    have hlen := (ambientLeaf hb r i).2
    simp only [SkewTree.forwardAuxB, ForwardAux, hlen]
    have hnlt : ¬ n < r.1.length := by omega
    have hne : n ≠ r.1.length := by omega
    simp [hnlt, hne]
  have h := star_skew hb SkewTree.forwardAuxB r.1
    (fun i => (ambientLeaf hb r i).1) r.2
    (fun i => (ambientLeaf hb r i).2)
    (direction_prefix_ambientLeaf hb r) haux
  simpa [star, ambientLeaves, List.map_ofFn] using h

end DualTree.UpLeafGeometry
