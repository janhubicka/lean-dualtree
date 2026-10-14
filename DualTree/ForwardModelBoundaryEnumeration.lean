import DualTree.ForwardModelHeapSurjective
import DualTree.ForwardModelBoundaryInterval

/-!
# Canonical finite enumeration of the corrected model boundary

The forward-heap bijection identifies the first `l` homogeneous
model vertices with indices `0, ..., l-1`. For `l>0`, the
previously proved boundary interval gives an **exact** indexing
of the canonical model boundary `A_l` by the consecutive heap
indices `l, ..., b*l`.

This module packages that indexing as an explicit equivalence

  {s : Node b // ModelBoundary l s} ≃ Fin (b*l-l+1)

and proves the resulting cardinality formula. In particular, the
bijection does not sort arbitrary node lists or choose an
unjustified permutation of children. Its index is defined by
the CORRECTED length-first forward order.

This is only the homogeneous model side of Definition 24.
No map from A_l to the literal source marker set R of a
semi-complete skew output is claimed here.
-/

namespace DualTree.ForwardModelBoundaryEnumeration

open ForwardModelBoundaryHeap
open ForwardModelBoundaryInterval
open ForwardModelHeapSurjective

/-- Evaluating the inverse forward-heap enumeration returns
the prescribed natural-number index. -/
theorem heapIndex_equiv_symm {b : Nat}
    (hb : 0 < b) (i : Nat) :
    heapIndex ((heapIndexEquivNat hb).symm i) = i := by
  change (heapIndexEquivNat hb)
    ((heapIndexEquivNat hb).symm i) = i
  exact (heapIndexEquivNat hb).apply_symm_apply i

/-- The corrected canonical model boundary A_l consists of
exactly the consecutive heap indices from l to b*l,
with the first boundary vertex indexed by zero in this
Fin enumeration. -/
noncomputable def boundaryIndexEquivFin {b l : Nat}
    (hb : 0 < b) (hl : 0 < l) :
    {s : Node b // ModelBoundary l s} ≃
      Fin (b * l - l + 1) where
  toFun := fun s => ⟨heapIndex s.1 - l, by
    have hrange :=
      (modelBoundary_iff_index_range hl s.1).1 s.2
    omega⟩
  invFun := fun i =>
    ⟨(heapIndexEquivNat hb).symm (i.val + l), by
      apply (modelBoundary_iff_index_range hl _).2
      have hbl : l ≤ b * l := by
        calc
          l = 1 * l := by simp
          _ ≤ b * l := Nat.mul_le_mul_right l (by omega)
      rw [heapIndex_equiv_symm hb (i.val + l)]
      have hi : i.val < b * l - l + 1 := i.isLt
      constructor <;> omega⟩
  left_inv := by
    intro s
    apply Subtype.ext
    change (heapIndexEquivNat hb).symm
      (heapIndex s.1 - l + l) = s.1
    have hlower : l ≤ heapIndex s.1 :=
      ((modelBoundary_iff_index_range hl s.1).1 s.2).1
    rw [Nat.sub_add_cancel hlower]
    exact (heapIndexEquivNat hb).symm_apply_apply s.1
  right_inv := by
    intro i
    apply Fin.ext
    change heapIndex ((heapIndexEquivNat hb).symm
      (i.val + l)) - l = i.val
    rw [heapIndex_equiv_symm hb (i.val + l)]
    omega

/-- The full b-ary model with l interior vertices has
exactly b*l-l+1 external boundary vertices. -/
theorem modelBoundary_card {b l : Nat}
    (hb : 0 < b) (hl : 0 < l) :
    Nat.card {s : Node b // ModelBoundary l s} =
      b * l - l + 1 := by
  calc
    Nat.card {s : Node b // ModelBoundary l s} =
        Nat.card (Fin (b * l - l + 1)) :=
      Nat.card_congr (boundaryIndexEquivFin hb hl)
    _ = b * l - l + 1 := by simp

end DualTree.ForwardModelBoundaryEnumeration
