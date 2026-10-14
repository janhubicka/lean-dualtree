import DualTree.ForwardModelHeapChildOrder

/-!
# Height bounds needed to interpret the model boundary in b^{<n}

Definition 24 defines its canonical first-l model interior and boundary
inside the FINITE homogeneous tree b^{<n}. The arithmetic forward heap
model was initially developed on unbounded finite lists of directions.

For b>0 the heap index increases by at least one at each new child.
Therefore every node s satisfies

    |s| ≤ heapIndex(s).

Consequently every first-l model interior vertex lies in b^{<n}
when l ≤ n, and every external boundary node lies in b^{<n}
when b*l < n. This is a convenient explicit sufficient ambient
height bound ensuring the unbounded model boundary agrees with the
finite-height object used in Definition 24.

These geometric facts are independent of the paper's invalid
reverse-lex auxiliary order. The exact canonical A-to-R address
and direction transport remains open.
-/

namespace DualTree.ForwardModelBoundaryHeight

open ForwardModelBoundaryHeap

/-- The forward breadth-first heap index is at least the
number of digits in the node, for positive branching. -/
private theorem length_add_le_foldl {b : Nat}
    (hb : 0 < b) :
    ∀ (s : Node b) (q : Nat),
      q + s.length ≤
        s.foldl (fun q i => b * q + 1 + i.val) q := by
  intro s
  induction s with
  | nil =>
      intro q
      simp
  | cons i tail ih =>
      intro q
      have hb1 : 1 ≤ b := by omega
      have hbase : q ≤ b * q := by
        calc
          q = 1 * q := by simp
          _ ≤ b * q := Nat.mul_le_mul_right q hb1
      have htail := ih (b * q + 1 + i.val)
      change q + (tail.length + 1) ≤
        tail.foldl (fun q i => b * q + 1 + i.val)
          (b * q + 1 + i.val)
      omega

/-- An ambient node has no more digits than its zero-based
forward-model heap index (for any positive arity). -/
theorem length_le_heapIndex {b : Nat}
    (hb : 0 < b)
    (s : Node b) :
    s.length ≤ heapIndex s := by
  have h := length_add_le_foldl hb s 0
  simpa [heapIndex] using h

/-- If the first l model nodes are requested and the ambient
homogeneous tree has n levels with l ≤ n, all those model
interior nodes actually exist inside b^{<n}. -/
theorem modelInterior_bounded_of_l_le_n {b l n : Nat}
    (hb : 0 < b)
    (hl : l ≤ n)
    (s : Node b)
    (hs : ModelInterior l s) :
    InHomTree n s := by
  change s.length < n
  have hlen := length_le_heapIndex hb s
  change heapIndex s < l at hs
  omega

/-- No external first-l model boundary marker is lost by
restricting the model to finite height n whenever n>b*l. -/
theorem modelBoundary_bounded_of_n_gt_b_mul_l {b l n : Nat}
    (hb : 0 < b)
    (hn : b * l < n)
    (s : Node b)
    (hs : ModelBoundary l s) :
    InHomTree n s := by
  change s.length < n
  have hlen := length_le_heapIndex hb s
  have hidx := modelBoundary_index_le hs
  omega

end DualTree.ForwardModelBoundaryHeight
