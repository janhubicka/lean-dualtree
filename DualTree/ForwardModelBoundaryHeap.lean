import DualTree.CutFrontier
import DualTree.MeetClosedFromBranching

/-!
# Arithmetic addresses for the canonical first-l model boundary

Definition 24 starts from the FIRST l nodes of the homogeneous b-ary
tree in its auxiliary breadth-first order, and takes all their
immediate ambient children outside those first l nodes.

A useful arithmetic code for the ordinary forward breadth-first
order is the zero-based b-ary heap index:
    index(∅) = 0,
    index(s ++ [i]) = b * index(s) + 1 + i.

This module introduces the heap code directly on finite list nodes.
For b>0, each ambient extension strictly increases its index.
Consequently the candidate first-l interior
    H_l = {s : index(s) < l}
is prefix-closed.

Its model external-child boundary
    A_l = { s ++ [i] : s∈H_l and s++[i]∉H_l }
is a prefix antichain and every boundary address has numeric
heap index in [l, b*l].

These are constructive general geometric facts used for the
remaining model-A-to-literal-R transport in corrected Lemma 27.

IMPORTANT: This module does NOT yet identify heap-index order
with the paper's printed REVERSE-lex auxiliary order (which
has an independent counterexample), nor prove that the
canonical direction map of an arbitrary forward-semi-complete
skew tree sends this arithmetic A_l onto its literal R markers.
The latter canonical transport remains open.
-/

namespace DualTree.ForwardModelBoundaryHeap

/-- The ordinary zero-based breadth-first b-ary heap address,
with directions numbered by their Fin b values. -/
def heapIndex {b : Nat} (s : Node b) : Nat :=
  s.foldl (fun q i => b * q + 1 + i.val) 0

/-- Attaching an actual immediate ambient child has the
standard b-ary heap-index formula. -/
theorem heapIndex_child {b : Nat}
    (s : Node b) (i : Fin b) :
    heapIndex (s ++ [i]) =
      b * heapIndex s + 1 + i.val := by
  simp [heapIndex, List.foldl_append]

/-- Every immediate extension raises its heap address for
positive branching (including the unary case b=1). -/
theorem heapIndex_lt_child {b : Nat}
    (hb : 0 < b)
    (s : Node b) (i : Fin b) :
    heapIndex s < heapIndex (s ++ [i]) := by
  have hmul : heapIndex s ≤ b * heapIndex s := by
    calc
      heapIndex s = 1 * heapIndex s := by simp
      _ ≤ b * heapIndex s :=
        Nat.mul_le_mul_right (heapIndex s) (by omega)
  rw [heapIndex_child]
  omega

/-- Appending any sequence of child directions cannot
decrease the breadth-first heap index. -/
theorem heapIndex_le_append {b : Nat}
    (hb : 0 < b)
    (s tail : Node b) :
    heapIndex s ≤ heapIndex (s ++ tail) := by
  induction tail generalizing s with
  | nil =>
      simp
  | cons i tail ih =>
      have hstep : heapIndex s ≤ heapIndex (s ++ [i]) :=
        Nat.le_of_lt (heapIndex_lt_child hb s i)
      have hrest :
          heapIndex (s ++ [i]) ≤
            heapIndex ((s ++ [i]) ++ tail) :=
        ih (s ++ [i])
      have hdecomp : s ++ (i :: tail) = (s ++ [i]) ++ tail := by
        simp [List.append_assoc]
      rw [hdecomp]
      exact hstep.trans hrest

/-- The arithmetic candidate for the initial l model vertices.
The equivalence with the corrected forward auxiliary order is
to be proved independently, not hidden in this definition. -/
def ModelInterior {b : Nat} (l : Nat) (s : Node b) : Prop :=
  heapIndex s < l

/-- The heap-initial interior is ambient prefix-closed when b>0. -/
theorem modelInterior_prefix_closed {b l : Nat}
    (hb : 0 < b)
    {s t : Node b}
    (hst : IsPrefix s t)
    (ht : ModelInterior l t) :
    ModelInterior l s := by
  rcases hst with ⟨tail, rfl⟩
  exact lt_of_le_of_lt (heapIndex_le_append hb s tail) ht

/-- External immediate children of the candidate model interior.
This models Definition 24's set A before transport to a skew tree. -/
def ModelBoundary {b : Nat} (l : Nat) (s : Node b) : Prop :=
  ¬ ModelInterior l s ∧
    ∃ p : Node b, ∃ i : Fin b,
      ModelInterior l p ∧ s = p ++ [i]

/-- A boundary child is excluded from the initial l model nodes;
hence its heap index is at least l. -/
theorem modelBoundary_index_ge {b l : Nat}
    {s : Node b}
    (hs : ModelBoundary l s) :
    l ≤ heapIndex s :=
  Nat.le_of_not_lt hs.1

/-- Every external child of the first l heap nodes has
heap address at most b*l. This is the exact numeric band
where Definition 24's model boundary must live. -/
theorem modelBoundary_index_le {b l : Nat}
    {s : Node b}
    (hs : ModelBoundary l s) :
    heapIndex s ≤ b * l := by
  obtain ⟨p, i, hp, hEq⟩ := hs.2
  subst s
  rw [heapIndex_child]
  have hlen : heapIndex p + 1 ≤ l :=
    Nat.succ_le_of_lt hp
  have hmul : b * (heapIndex p + 1) ≤ b * l :=
    Nat.mul_le_mul_left b hlen
  have hdir : 1 + i.val ≤ b := by
    have h := i.isLt
    omega
  have hbound :
      b * heapIndex p + 1 + i.val ≤
        b * (heapIndex p + 1) := by
    simp only [Nat.mul_add]
    omega
  exact hbound.trans hmul

/-- Distinct external children of an ambient prefix-closed
interior are incomparable. In particular the actual model A_l
is a prefix antichain, with no need for a tie-break order. -/
theorem modelBoundary_antichain {b l : Nat}
    (hb : 0 < b)
    {s t : Node b}
    (hs : ModelBoundary l s)
    (ht : ModelBoundary l t)
    (hst : IsPrefix s t) :
    s = t := by
  by_cases heq : s = t
  · exact heq
  obtain ⟨p, i, hp, hpEq⟩ := ht.2
  have hstrict : IsStrictPrefix s t := ⟨hst, heq⟩
  have hlen : s.length < t.length :=
    MeetClosedFromBranching.length_lt_of_strictPrefix hstrict
  have hparentlen : t.length = p.length + 1 := by
    rw [hpEq]
    simp
  have hle : s.length ≤ p.length := by omega
  have hpt : IsPrefix p t := ⟨[i], hpEq⟩
  have hsp : IsPrefix s p :=
    CutFrontier.prefix_of_prefix_length_le hst hpt hle
  exact False.elim (hs.1 (modelInterior_prefix_closed hb hsp hp))

end DualTree.ForwardModelBoundaryHeap
