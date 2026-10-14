import DualTree.ForwardModelBoundaryInterval

/-!
# Ordering the children of the arithmetic forward model

The corrected Lemma 27 requires a direction-preserving transport
of the canonical first-l model boundary A to the literal first-exit
markers R of a semi-complete skew source. Numerical cardinalities
alone are insufficient: each source direction must be preserved.

The forward breadth-first heap formula gives two precise ordering
facts, independent of complete or semi-complete source geometry:

* at a fixed parent s, child directions i<j have increasing indices;
* if the heap index of parent s precedes that of parent t, EVERY
  child of s precedes EVERY child of t, whatever the directions.

Together they express the stable block order of model children.
They do not yet prove that the global heap index is an isomorphism
with the ForwardAux shortlex order, or construct the actual A-to-R
canonical transport. Those remain separate proof obligations.
-/

namespace DualTree.ForwardModelHeapChildOrder

open ForwardModelBoundaryHeap

/-- Child directions at one parent occur in increasing order
in the model's arithmetic breadth-first enumeration. -/
theorem heapIndex_child_lt_of_direction_lt {b : Nat}
    (s : Node b) (i j : Fin b) (hij : i < j) :
    heapIndex (s ++ [i]) < heapIndex (s ++ [j]) := by
  rw [heapIndex_child, heapIndex_child]
  have h : i.val < j.val := hij
  omega

/-- The entire block of b children of an earlier-indexed
model parent lies before the entire block of children of
a later-indexed parent. There is no restriction on the
particular child directions i,j. -/
theorem heapIndex_child_lt_of_parent_lt {b : Nat}
    (s t : Node b) (i j : Fin b)
    (hst : heapIndex s < heapIndex t) :
    heapIndex (s ++ [i]) < heapIndex (t ++ [j]) := by
  have hparent : heapIndex s + 1 ≤ heapIndex t :=
    Nat.succ_le_of_lt hst
  have hmul : b * (heapIndex s + 1) ≤ b * heapIndex t :=
    Nat.mul_le_mul_left b hparent
  have hi : i.val < b := i.isLt
  rw [heapIndex_child, heapIndex_child]
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- Child blocks are lexicographically ordered by their
parent's heap index and then by the direction. This is the
finite-order arithmetic needed to align model boundary A
with sorted forward signature frontiers. -/
theorem heapIndex_child_lt_of_parent_or_direction {b : Nat}
    (s t : Node b) (i j : Fin b)
    (h : heapIndex s < heapIndex t ∨
         (heapIndex s = heapIndex t ∧ i < j)) :
    heapIndex (s ++ [i]) < heapIndex (t ++ [j]) := by
  rcases h with hparent | ⟨heq, hij⟩
  · exact heapIndex_child_lt_of_parent_lt s t i j hparent
  · rw [heapIndex_child, heapIndex_child, heq]
    have hv : i.val < j.val := hij
    omega

end DualTree.ForwardModelHeapChildOrder
