import DualTree.SkewTree
import DualTree.Lemma27Audit
import Mathlib

/-!
# Visible ancestor variables in Lemma 27

The printed map R_i attempts to cover all variables in Int(S_w) with the
m'+1 auxiliary symbols.  The legal targets in a given cone are only those
interior variables rooted at strict ancestors of its frontier node t_i.

This file isolates the finite bound needed for that repair.  The list of
visible ancestors is a filter of Pred_T(t_i), so its cardinality is at most
the intrinsic height of t_i.  Every nonempty target list of size at most
m'+1 can be covered by m'+1 auxiliary symbol indices.

The remaining geometric proof obligation is to identify the exact ancestor
list of each frontier cone in the signature construction of Lemma 27.
-/

namespace DualTree.Lemma27Repair

/-- A general length bound for a filtered finite list. -/
theorem filter_length_le {α : Type*}
    (xs : List α) (p : α → Bool) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x with
      | false =>
          simpa [List.filter_cons, hp] using
            (Nat.le_trans ih (Nat.le_succ xs.length))
      | true =>
          simpa [List.filter_cons, hp] using (Nat.succ_le_succ ih)

/-- Interior variable roots of I visible from the frontier t in T. -/
def visibleAncestors {b : Nat}
    (T I : List (Node b)) (t : Node b) : List (Node b) :=
  (SkewTree.preds T t).filter (fun s => decide (s ∈ I))

theorem visibleAncestors_length_le_height {b : Nat}
    (T I : List (Node b)) (t : Node b) :
    (visibleAncestors T I t).length ≤ SkewTree.heightAt T t := by
  unfold visibleAncestors SkewTree.heightAt
  exact filter_length_le (SkewTree.preds T t)
    (fun s => decide (s ∈ I))

/-- Intrinsic height at most m'+1 bounds the number of visible roots. -/
theorem visibleAncestors_length_le_aux {b m : Nat}
    (T I : List (Node b)) (t : Node b)
    (ht : SkewTree.heightAt T t ≤ m + 1) :
    (visibleAncestors T I t).length ≤ m + 1 :=
  (visibleAncestors_length_le_height T I t).trans ht

/-- There is a surjection from m'+1 labels onto any nonempty k≤m'+1 list indices. -/
theorem auxiliary_symbols_cover_indices
    (m k : Nat) (hk : 0 < k) (hkm : k ≤ m + 1) :
    ∃ R : Fin (m + 1) → Fin k, Function.Surjective R := by
  let R : Fin (m + 1) → Fin k := fun i =>
    if h : i.val < k then ⟨i.val, h⟩ else ⟨0, hk⟩
  refine ⟨R, ?_⟩
  intro j
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hkm⟩, ?_⟩
  simp [R, j.isLt]

/--
The restricted ancestor list can be indexed by auxiliary symbols whenever
it is nonempty and its frontier has intrinsic height at most m'+1.
-/
theorem visibleAncestors_auxiliary_coverage {b m : Nat}
    (T I : List (Node b)) (t : Node b)
    (hfront : SkewTree.heightAt T t ≤ m + 1)
    (hnonempty : 0 < (visibleAncestors T I t).length) :
    ∃ R : Fin (m + 1) → Fin (visibleAncestors T I t).length,
      Function.Surjective R :=
  auxiliary_symbols_cover_indices m
    (visibleAncestors T I t).length hnonempty
    (visibleAncestors_length_le_aux T I t hfront)

end DualTree.Lemma27Repair
