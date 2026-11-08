import DualTree.HigherConeRectangular

/-!
# Track C: real bounded tree cells underlying root and cone bands

A flat root/cone matrix is not automatically a word indexed by the actual
ambient finite tree. These constructions produce honest nodes of the SAME
finite b-branching tree, prove that the two bands do not intersect, and
establish uniqueness of their level indices. Geometry of the chosen b
different branch prefixes, and the full word transport, remain separate.
-/

namespace DualTree.HigherTreeCells

open HigherConeAddresses

/-- The length-j all-zero node in the root band of b^(<N+M). -/
def rootBandCell {b N M : Nat} (hb : 0 < b) (j : Fin N) :
    BoundedNode b (N + M) :=
  ⟨List.replicate j.val ⟨0, hb⟩, by
    change (List.replicate j.val (⟨0, hb⟩ : Fin b)).length < N + M
    have hj : j.val < N := j.isLt
    simp only [List.length_replicate]
    omega⟩

/-- At each depth-N address a, append the all-zero tail of length j. This
is a true node of the ambient finite tree, not an abstract matrix index. -/
def coneBandCell {b N M : Nat} (hb : 0 < b)
    (a : Address b N) (j : Fin M) :
    BoundedNode b (N + M) :=
  ⟨addressNode a ++ List.replicate j.val ⟨0, hb⟩, by
    change (addressNode a ++
      List.replicate j.val (⟨0, hb⟩ : Fin b)).length < N + M
    have hj : j.val < M := j.isLt
    simp only [List.length_append, List.length_replicate, addressNode_length]
    omega⟩

theorem rootBandCell_length {b N M : Nat}
    (hb : 0 < b) (j : Fin N) :
    (rootBandCell (M := M) hb j).1.length = j.val := by
  simp [rootBandCell]

theorem coneBandCell_length {b N M : Nat}
    (hb : 0 < b) (a : Address b N) (j : Fin M) :
    (coneBandCell hb a j).1.length = N + j.val := by
  simp [coneBandCell, addressNode_length]

/-- The root band contains exactly one canonical zero-spine cell at each
depth, and distinct flat root positions never denote the same tree node. -/
theorem rootBandCell_injective {b N M : Nat}
    (hb : 0 < b) :
    Function.Injective (rootBandCell (M := M) hb) := by
  intro i j hij
  have hlen := congrArg
    (fun s : BoundedNode b (N + M) => s.1.length) hij
  simp only [rootBandCell_length] at hlen
  exact Fin.ext hlen

/-- Root and cone coordinates have disjoint ambient level ranges.
This prevents the flat Hales--Jewett root and cone symbols from overwriting
each other when transported into a single actual tree word. -/
theorem rootBandCell_ne_coneBandCell {b N M : Nat}
    (hb : 0 < b) (j : Fin N) (a : Address b N) (k : Fin M) :
    rootBandCell (M := M) hb j ≠ coneBandCell hb a k := by
  intro h
  have hlen := congrArg
    (fun s : BoundedNode b (N + M) => s.1.length) h
  simp only [rootBandCell_length, coneBandCell_length] at hlen
  have hj : j.val < N := j.isLt
  omega

/-- If two cone cells agree, they must originate at the same cone-band
level. The remaining address-injectivity lemma is still needed for the
complete flat-to-tree dictionary. -/
theorem coneBandCell_equal_implies_same_level {b N M : Nat}
    (hb : 0 < b) (a a' : Address b N) (j k : Fin M)
    (h : coneBandCell hb a j = coneBandCell hb a' k) : j = k := by
  have hlen := congrArg
    (fun s : BoundedNode b (N + M) => s.1.length) h
  simp only [coneBandCell_length] at hlen
  apply Fin.ext
  omega

/-- A complete cone-band coordinate (address, depth) is recovered uniquely
from its physical bounded tree node. No two independent addresses collapse. -/
theorem coneBandCell_pair_injective {b N M : Nat}
    (hb : 0 < b) :
    Function.Injective (fun p : Address b N × Fin M =>
      coneBandCell hb p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨a, j⟩
  rcases q with ⟨a', k⟩
  have hj : j = k :=
    coneBandCell_equal_implies_same_level hb a a' j k hpq
  subst k
  have hlist :
      addressNode a ++ List.replicate j.val (⟨0, hb⟩ : Fin b) =
      addressNode a' ++ List.replicate j.val (⟨0, hb⟩ : Fin b) :=
    congrArg (fun s : BoundedNode b (N + M) => s.1) hpq
  have haddr : addressNode a = addressNode a' :=
    List.append_left_injective
      (List.replicate j.val (⟨0, hb⟩ : Fin b)) hlist
  have ha : a = a' :=
    List.ofFn_injective (by simpa [addressNode] using haddr)
  subst a'
  rfl

end DualTree.HigherTreeCells
