import DualTree.HigherBranchPrefix
import DualTree.HigherSkewGeometry

/-!
# Track C: complete-skew geometry of the ACTUAL chosen HJ support

The support positions come from the earliest root variable and the earliest
cone variable, with b distinct actual depth-N selected addresses. Using the
proved direction-prefix lemma and the general star construction, we certify
the full k=2 complete-skew condition and both vector level-order conditions.
There are explicit certificates for both the paper and forward auxiliary
orders. This is geometric: no Hales--Jewett tree-variable-word realization
or monochromatic span theorem is asserted here.
-/

namespace DualTree.HigherPhysicalComplete

open HigherPhysicalSupport
open HigherBranchPrefix

/-- Forget boundedness on the actual HJ-selected support. -/
def supportNodes {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) : List (Node b) :=
  (support hb r s).map Subtype.val

theorem supportNodes_eq_star {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    supportNodes hb r s =
      UpLeafGeometry.star (root (M := M) hb r).1
        (fun i : Fin b => (child hb r s i).1) := by
  simp [supportNodes, support, UpLeafGeometry.star,
    List.map_ofFn, Function.comp_def]

private theorem root_length_lt_child_level {b N M : Nat}
    (hb : 0 < b) (r : Fin N) (s : Fin M) :
    (root (M := M) hb r).1.length < N + s.val := by
  rw [show (root (M := M) hb r).1.length = r.val
    from HigherTreeCells.rootBandCell_length hb r]
  have hr : r.val < N := r.isLt
  omega

private theorem paperAux_false_of_length_lt {b : Nat}
    (x y : Node b) (h : y.length < x.length) :
    SkewTree.paperAuxB x y = false := by
  have hn : ¬ PaperAux x y := by
    rintro (hxy | ⟨heq, _⟩)
    · omega
    · omega
  simp [SkewTree.paperAuxB, hn]

private theorem forwardAux_false_of_length_lt {b : Nat}
    (x y : Node b) (h : y.length < x.length) :
    SkewTree.forwardAuxB x y = false := by
  have hn : ¬ ForwardAux x y := by
    rintro (hxy | ⟨heq, _⟩)
    · omega
    · omega
  simp [SkewTree.forwardAuxB, hn]

/-- Once later leaves are not ordered before the shorter support root,
the HJ-selected physical root and b selected children form a genuine
k=2 complete-skew star, not a singleton surrogate. -/
theorem complete_two_of_aux
    {b N M : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Fin N) (s : Fin M)
    (haux : ∀ dir : Fin b,
      aux (child hb r s dir).1 (root (M := M) hb r).1 = false) :
    SkewTree.completeB aux 2 (supportNodes hb r s) = true := by
  let R : Node b := (root (M := M) hb r).1
  let leaf : Fin b → Node b := fun i => (child hb r s i).1
  have hr : R.length < N + s.val :=
    root_length_lt_child_level hb r s
  have hlen : ∀ i, (leaf i).length = N + s.val :=
    fun i => child_level hb r s i
  have hbranch : ∀ i, IsPrefix (R ++ [i]) (leaf i) :=
    fun i => root_branch_prefix_child hb r s i
  have hskew : SkewTree.skewB aux (UpLeafGeometry.star R leaf) = true :=
    UpLeafGeometry.star_skew hb aux R leaf hr hlen hbranch haux
  rw [supportNodes_eq_star]
  exact HigherSkewGeometry.star_complete_two_of_skew hb aux
    R leaf hr hlen hbranch hskew

/-- The same genuine HJ-selected star in every vector coordinate has
all cross-coordinate comparisons, including different intrinsic levels. -/
theorem vector_complete_two_of_aux
    {b N M d : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Fin N) (s : Fin M)
    (haux : ∀ dir : Fin b,
      aux (child hb r s dir).1 (root (M := M) hb r).1 = false) :
    VectorSkew.vectorCompleteB aux 2
      (fun _ : Fin d => supportNodes hb r s) = true := by
  let R : Node b := (root (M := M) hb r).1
  let leaf : Fin b → Node b := fun i => (child hb r s i).1
  have hr : R.length < N + s.val :=
    root_length_lt_child_level hb r s
  have hlen : ∀ i, (leaf i).length = N + s.val :=
    fun i => child_level hb r s i
  have hbranch : ∀ i, IsPrefix (R ++ [i]) (leaf i) :=
    fun i => root_branch_prefix_child hb r s i
  have hskew : SkewTree.skewB aux (UpLeafGeometry.star R leaf) = true :=
    UpLeafGeometry.star_skew hb aux R leaf hr hlen hbranch haux
  rw [supportNodes_eq_star]
  exact HigherSkewGeometry.star_vector_complete_two_of_skew
    (d := d) hb aux R leaf hr hlen hbranch hskew

theorem complete_two_paper {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    SkewTree.completeB SkewTree.paperAuxB 2
      (supportNodes hb r s) = true := by
  apply complete_two_of_aux hb SkewTree.paperAuxB r s
  intro dir
  exact paperAux_false_of_length_lt _ _
    (root_level_lt_child hb r s dir)

theorem complete_two_forward {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    SkewTree.completeB SkewTree.forwardAuxB 2
      (supportNodes hb r s) = true := by
  apply complete_two_of_aux hb SkewTree.forwardAuxB r s
  intro dir
  exact forwardAux_false_of_length_lt _ _
    (root_level_lt_child hb r s dir)

theorem vector_complete_two_paper {b N M d : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 2
      (fun _ : Fin d => supportNodes hb r s) = true := by
  apply vector_complete_two_of_aux hb SkewTree.paperAuxB r s
  intro dir
  exact paperAux_false_of_length_lt _ _
    (root_level_lt_child hb r s dir)

theorem vector_complete_two_forward {b N M d : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 2
      (fun _ : Fin d => supportNodes hb r s) = true := by
  apply vector_complete_two_of_aux hb SkewTree.forwardAuxB r s
  intro dir
  exact forwardAux_false_of_length_lt _ _
    (root_level_lt_child hb r s dir)

end DualTree.HigherPhysicalComplete
