import DualTree.ForwardModelBoundaryHeap

/-!
# Exact arithmetic interval of the canonical first-l model boundary

For positive l, the candidate Definition 24 canonical model boundary
formed by all external immediate children of the first l heap-indexed
vertices has a particularly simple description:

  ModelBoundary l s  ↔  l ≤ heapIndex s ∧ heapIndex s ≤ b*l.

The forward implication was established in ForwardModelBoundaryHeap.
For the converse, the index range excludes the root (index zero).
Every nonempty finite node decomposes uniquely as p ++ [i].
If its parent p had heap index at least l, then its child's
heap index would exceed b*l, contradicting the bound.
Therefore p belongs to the initial model interior.

This result holds for all arities b (including b=0, when the
interval is vacuous); the positive-l hypothesis is necessary:
for l=0 the index-zero root satisfies the degenerate interval
but the model interior and boundary are empty.

The exact interval establishes an arithmetic model for the A
side of Definition 24, but does not yet prove that heapIndex
is a bijection with the nonnegative integers for b>0, nor
that it matches the globally corrected forward auxiliary
order and the actual literal signature markers R.
-/

namespace DualTree.ForwardModelBoundaryInterval

open ForwardModelBoundaryHeap

/-- Any ambient heap-index address in [l,b*l] is exactly an
external child of the initial l model interior, for l>0. -/
theorem modelBoundary_of_index_range {b l : Nat}
    (hl : 0 < l)
    (s : Node b)
    (hlo : l ≤ heapIndex s)
    (hhi : heapIndex s ≤ b * l) :
    ModelBoundary l s := by
  have hnot : ¬ ModelInterior l s := by
    change ¬ heapIndex s < l
    omega
  cases hrev : s.reverse with
  | nil =>
      have hs : s = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      subst s
      simp [heapIndex] at hlo
      omega
  | cons i revParent =>
      let p : Node b := revParent.reverse
      have hs : s = p ++ [i] := by
        have h := congrArg List.reverse hrev
        simpa [p] using h
      have hparent : ModelInterior l p := by
        change heapIndex p < l
        by_contra hbad
        have hge : l ≤ heapIndex p := Nat.le_of_not_lt hbad
        have hmul : b * l ≤ b * heapIndex p :=
          Nat.mul_le_mul_left b hge
        have hchild :
            heapIndex s = b * heapIndex p + 1 + i.val := by
          rw [hs]
          exact heapIndex_child p i
        omega
      exact ⟨hnot, ⟨p, i, hparent, hs⟩⟩

/-- Exact contiguous heap-index band of the candidate
Definition 24 boundary, not just the earlier necessary bound. -/
theorem modelBoundary_iff_index_range {b l : Nat}
    (hl : 0 < l)
    (s : Node b) :
    ModelBoundary l s ↔
      l ≤ heapIndex s ∧ heapIndex s ≤ b * l := by
  constructor
  · intro h
    exact ⟨modelBoundary_index_ge h, modelBoundary_index_le h⟩
  · rintro ⟨hlo, hhi⟩
    exact modelBoundary_of_index_range hl s hlo hhi

end DualTree.ForwardModelBoundaryInterval
