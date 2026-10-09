import DualTree.CanonicalConeCoordinates

/-!
# Injective padding of bounded prefix antichains to a common level

For the missing Lemma 27 numerical estimate d ≤ b^(m'+1), one may
transfer the outside-cut support frontier to source addresses by the
canonical prefix-tree isomorphism. The resulting addresses form a
prefix antichain, each with length at most m'+1.

This file checks the elementary coding step independent of T:
pad every address by a fixed direction to a common length. Two
addresses which give the same padded word must be prefix-comparable.
Hence padding is injective on any prefix antichain.

The final estimate still requires specializing this to the exact
frontier list, ensuring its source addresses have the required length
bound, and counting full-level b-ary words. No b^n cardinality
theorem is asserted in this module.
-/

namespace DualTree.FrontierAntichainPadding

/-- Extend a finite address to a requested length by one fixed direction,
when the requested length is large enough. -/
def pad {b : Nat} (fill : Fin b)
    (depth : Nat) (u : Node b) : Node b :=
  u ++ List.replicate (depth - u.length) fill

/-- The source address is an initial segment of its padded code. -/
theorem prefix_pad {b : Nat} (fill : Fin b)
    (depth : Nat) (u : Node b) :
    IsPrefix u (pad fill depth u) := by
  exact ⟨List.replicate (depth - u.length) fill, rfl⟩

/-- Padding has exactly the requested length when the budget permits it. -/
theorem pad_length {b : Nat} (fill : Fin b)
    (depth : Nat) (u : Node b) (hu : u.length ≤ depth) :
    (pad fill depth u).length = depth := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

/-- Equal padded words come from comparable original addresses. -/
theorem comparable_of_pad_eq {b : Nat}
    (fill : Fin b) (depth : Nat) (u v : Node b)
    (hpad : pad fill depth u = pad fill depth v) :
    IsPrefix u v ∨ IsPrefix v u := by
  rcases le_total u.length v.length with hle | hle
  · have hu : IsPrefix u (pad fill depth v) := by
      rw [← hpad]
      exact prefix_pad fill depth u
    exact Or.inl (CutFrontier.prefix_of_prefix_length_le
      hu (prefix_pad fill depth v) hle)
  · have hv : IsPrefix v (pad fill depth u) := by
      rw [hpad]
      exact prefix_pad fill depth v
    exact Or.inr (CutFrontier.prefix_of_prefix_length_le
      hv (prefix_pad fill depth u) hle)

/-- A prefix antichain never has two distinct nodes with equal padded codes. -/
theorem eq_of_pad_eq_antichain {b : Nat}
    (F : List (Node b))
    (hanti : ∀ u v, u ∈ F → v ∈ F → IsPrefix u v → u = v)
    (fill : Fin b) (depth : Nat)
    {u v : Node b} (hu : u ∈ F) (hv : v ∈ F)
    (heq : pad fill depth u = pad fill depth v) :
    u = v := by
  rcases comparable_of_pad_eq fill depth u v heq with h | h
  · exact hanti u v hu hv h
  · exact (hanti v u hv hu h).symm

/-- Padding is injective on the whole finite prefix antichain. -/
theorem pad_injective_on_antichain {b : Nat}
    (F : List (Node b))
    (hanti : ∀ u v, u ∈ F → v ∈ F → IsPrefix u v → u = v)
    (fill : Fin b) (depth : Nat) :
    Set.InjOn (pad fill depth) {u : Node b | u ∈ F} := by
  intro u hu v hv heq
  exact eq_of_pad_eq_antichain F hanti fill depth hu hv heq

end DualTree.FrontierAntichainPadding
