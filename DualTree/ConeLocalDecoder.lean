import DualTree.LiteralFrontierCleanup
import DualTree.VisibleAncestors

/-!
# Local auxiliary alphabet for the cone coding of Lemma 27

The printed proof asks for a map from m'+1 auxiliary letters onto all
interior variables of the reconstructed starred word.  Such a map may
not exist and may refer to variables incomparable with the given cone.

The corrected local target is the list of interior variable roots
among the proper support predecessors of the cone frontier.  This
file supplies a total decoder from the auxiliary alphabet, using the
fixed fallback letter when that list is empty.  When nonempty, all
visible ancestor positions occur.  No claim is made that the
frontier-height bound needed for the decoder follows from the paper.
-/

namespace DualTree.ConeLocalDecoder

/-- A visible ancestor belongs to both lists and properly precedes its frontier. -/
theorem visibleAncestor_spec {b : Nat}
    (T I : List (Node b)) (frontier r : Node b)
    (hr : r ∈ Lemma27Repair.visibleAncestors T I frontier) :
    r ∈ T ∧ r ∈ I ∧ IsStrictPrefix r frontier := by
  unfold Lemma27Repair.visibleAncestors at hr
  rcases List.mem_filter.mp hr with ⟨hpred, hI⟩
  have hrI : r ∈ I := by simpa using hI
  unfold SkewTree.preds at hpred
  rcases List.mem_filter.mp hpred with ⟨hrT, hprefix⟩
  exact ⟨hrT, hrI,
    (SkewBranchGeometry.strictPrefixB_iff r frontier).1 hprefix⟩

/-- The element at any visible-ancestor index is a proper frontier predecessor. -/
theorem visibleAncestor_get_prefix {b : Nat}
    (T I : List (Node b)) (frontier : Node b)
    (j : Fin (Lemma27Repair.visibleAncestors T I frontier).length) :
    IsStrictPrefix
      ((Lemma27Repair.visibleAncestors T I frontier).get j) frontier := by
  exact (visibleAncestor_spec T I frontier _
    (List.get_mem (Lemma27Repair.visibleAncestors T I frontier) j)).2.2

/-- Choose a surjection from the auxiliary symbols onto a nonempty target. -/
noncomputable def indexMap
    (m k : Nat) (hk : 0 < k) (hkm : k ≤ m + 1) :
    Fin (m + 1) → Fin k :=
  Classical.choose (Lemma27Repair.auxiliary_symbols_cover_indices m k hk hkm)

/-- Every visible target position occurs in this chosen index map. -/
theorem indexMap_surjective
    (m k : Nat) (hk : 0 < k) (hkm : k ≤ m + 1) :
    Function.Surjective (indexMap m k hk hkm) :=
  Classical.choose_spec (Lemma27Repair.auxiliary_symbols_cover_indices
    m k hk hkm)

/--
The typed decoder for one frontier.  The variable alternative contains
a position in the list of visible ancestor roots, not an arbitrary
variable of the reconstructed starred word.
-/
noncomputable def decode
    {b m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1) :
    Fin (m + 1) →
      Sum α (Fin (Lemma27Repair.visibleAncestors T I frontier).length) := by
  classical
  let k := (Lemma27Repair.visibleAncestors T I frontier).length
  if hk : 0 < k then
    exact fun i => Sum.inr
      (indexMap m k hk
        (Lemma27Repair.visibleAncestors_length_le_aux
          T I frontier hfront) i)
  else
    exact fun _ => Sum.inl a

/-- With no visible ancestor, all auxiliary symbols decode to the fallback letter. -/
theorem decode_empty
    {b m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (hzero : (Lemma27Repair.visibleAncestors T I frontier).length = 0)
    (i : Fin (m + 1)) :
    decode T I frontier a hfront i = Sum.inl a := by
  simp [decode, hzero]

/-- Otherwise the decoder covers every visible ancestor position. -/
theorem decode_onto_visible
    {b m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (hpos : 0 < (Lemma27Repair.visibleAncestors T I frontier).length)
    (j : Fin (Lemma27Repair.visibleAncestors T I frontier).length) :
    ∃ i : Fin (m + 1),
      decode T I frontier a hfront i = Sum.inr j := by
  let k := (Lemma27Repair.visibleAncestors T I frontier).length
  have hbound :
      k ≤ m + 1 :=
    Lemma27Repair.visibleAncestors_length_le_aux
      T I frontier hfront
  rcases indexMap_surjective m k hpos hbound j with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simp [decode, k, hpos, hi]

/-- Decode the visible-ancestor index to its actual root in the support. -/
noncomputable def decodeRoot
    {b m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (i : Fin (m + 1)) :
    Sum α (Node b) :=
  match decode T I frontier a hfront i with
  | Sum.inl c => Sum.inl c
  | Sum.inr j =>
      Sum.inr ((Lemma27Repair.visibleAncestors T I frontier).get j)

/-- The decoder never emits a variable whose root is outside the given cone path. -/
theorem decodeRoot_prefix
    {b m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (i : Fin (m + 1))
    (r : Node b)
    (hr : decodeRoot T I frontier a hfront i = Sum.inr r) :
    IsStrictPrefix r frontier := by
  unfold decodeRoot at hr
  cases hdecode : decode T I frontier a hfront i with
  | inl c =>
      simp [hdecode] at hr
  | inr j =>
      have hroot :
          ((Lemma27Repair.visibleAncestors T I frontier).get j) = r := by
        simpa [hdecode] using hr
      rw [← hroot]
      exact visibleAncestor_get_prefix T I frontier j

end DualTree.ConeLocalDecoder
