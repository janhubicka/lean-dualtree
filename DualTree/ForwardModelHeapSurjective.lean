import DualTree.ForwardModelHeapInjective

/-!
# The corrected forward heap enumeration is onto the natural numbers

For each positive branching b, the zero-based b-ary heap map
is not only injective and forward-order-preserving: it is SURJECTIVE.

For a nonzero index k+1, choose the parent index q = k / b and
the last direction i = k % b. Since q ≤ k < k+1, strong induction
produces a parent node p with heapIndex(p) = q. The child
p ++ [i] then has index
    b*(k/b)+1+(k%b)=k+1.

Together with the proved injectivity and the exact ForwardAux
order equivalence, this makes the arithmetic heap model an
order isomorphism between the homogeneous tree and the
natural numbers, equipped with length-first FORWARD lex order.

In particular the candidate first-l interior H_l has EXACTLY
l nodes, now not merely a numerical predicate on an
unspecified subset of the model. The canonical image of the
finite first-l boundary A in an arbitrary forward-semi-complete
skew tree is still a separate geometric transport theorem.
-/

namespace DualTree.ForwardModelHeapSurjective

open ForwardModelBoundaryHeap
open ForwardModelHeapInjective

/-- Every natural number has an actual finite b-ary direction
sequence of exactly that heap index, for b>0. -/
theorem heapIndex_surjective {b : Nat}
    (hb : 0 < b) :
    Function.Surjective (heapIndex (b := b)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨[], rfl⟩
      | succ k =>
          let i : Fin b := ⟨k % b, Nat.mod_lt k hb⟩
          have hq : k / b < k + 1 := by
            have hle : k / b ≤ k := Nat.div_le_self k b
            omega
          obtain ⟨p, hp⟩ := ih (k / b) hq
          refine ⟨p ++ [i], ?_⟩
          rw [heapIndex_child, hp]
          change b * (k / b) + 1 + k % b = k + 1
          have hmod : k % b + b * (k / b) = k :=
            Nat.mod_add_div k b
          omega

/-- The forward heap index is an actual bijection between all
finite b-ary direction words and natural numbers (b>0). -/
noncomputable def heapIndexEquivNat {b : Nat}
    (hb : 0 < b) : Node b ≃ Nat :=
  Equiv.ofBijective (heapIndex (b := b))
    ⟨heapIndex_injective hb, heapIndex_surjective hb⟩

/-- The first l model heap nodes are canonically indexed by
Fin l, with no arbitrary choices or missing indices. -/
noncomputable def initialModelEquiv {b : Nat}
    (hb : 0 < b) (l : Nat) :
    Fin l ≃ {s : Node b // ModelInterior l s} where
  toFun := fun i =>
    ⟨(heapIndexEquivNat hb).symm i.val, by
      change (heapIndexEquivNat hb) ((heapIndexEquivNat hb).symm i.val) < l
      simpa only [Equiv.apply_symm_apply] using i.isLt⟩
  invFun := fun s => ⟨heapIndex s.1, s.2⟩
  left_inv := by
    intro i
    apply Fin.ext
    exact (heapIndexEquivNat hb).apply_symm_apply i.val
  right_inv := by
    intro s
    apply Subtype.ext
    exact (heapIndexEquivNat hb).symm_apply_apply s.1

/-- The forward arithmetic first-l interior has exactly l
vertices, now justified by the explicit heap-bijection. -/
theorem modelInterior_card {b : Nat}
    (hb : 0 < b) (l : Nat) :
    Nat.card {s : Node b // ModelInterior l s} = l := by
  calc
    Nat.card {s : Node b // ModelInterior l s} =
        Nat.card (Fin l) :=
      Nat.card_congr (initialModelEquiv hb l).symm
    _ = l := by simp

end DualTree.ForwardModelHeapSurjective
