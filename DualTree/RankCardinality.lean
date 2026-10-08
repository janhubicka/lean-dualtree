import Mathlib

/-!
# Finite rank counting

If a duplicate-free list has pairwise distinct natural-number ranks
bounded by m, its length is at most m+1. This elementary counting
lemma is needed to bound the intrinsic height of support frontiers
in the proof of Lemma 27.
-/

namespace DualTree.RankCardinality

/-- Distinct bounded ranks give a bound on the length of a finite list. -/
theorem nodup_length_le_of_rank_bound
    {β : Type*}
    (xs : List β) (m : Nat) (rank : β → Nat)
    (hnd : xs.Nodup)
    (hbound : ∀ x, x ∈ xs → rank x ≤ m)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → rank x = rank y → x = y) :
    xs.length ≤ m + 1 := by
  classical
  let s : Finset β := xs.toFinset
  let t : Finset Nat := Finset.range (m + 1)
  have hmap : Set.MapsTo rank (↑s) (↑t) := by
    intro x hx
    have hx' : x ∈ xs := by simpa [s] using hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx'))
  have hinjOn : Set.InjOn rank (↑s) := by
    intro x hx y hy hxy
    have hx' : x ∈ xs := by simpa [s] using hx
    have hy' : y ∈ xs := by simpa [s] using hy
    exact hinj x hx' y hy' hxy
  have hc : s.card ≤ t.card :=
    Finset.card_le_card_of_injOn rank hmap hinjOn
  simpa [s, t, List.toFinset_card_of_nodup hnd] using hc

end DualTree.RankCardinality
