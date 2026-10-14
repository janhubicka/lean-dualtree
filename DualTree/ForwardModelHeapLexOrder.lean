import DualTree.ForwardModelBoundaryHeight

/-!
# Forward lexicographic order and arithmetic heap indices at one level

Definition 24's candidate canonical model H_l is indexed by a
forward breadth-first heap enumeration. The corrected auxiliary
order compares length first and then the ordinary FORWARD lex order.

The stable child-block inequalities verified in
ForwardModelHeapChildOrder make it possible to compare arbitrary
equal-length source suffixes with a common prefix:

* a strict inequality of the parent heap addresses stays strict
  after any two same-length appended direction lists;
* ordinary forward lex order on two same-length suffixes is
  reflected by nondecreasing heap indices after any common prefix;
* conversely a strict heap-index comparison on one homogeneous
  level forces the corresponding forward lex comparison.

These are source-level model facts, independent of any source
semi-complete skew support. Distinct-level heap/length ordering,
global index injectivity, and the direction-preserving canonical
A-to-literal-R transport are still separate obligations.
-/

namespace DualTree.ForwardModelHeapLexOrder

open ForwardModelBoundaryHeap
open ForwardModelHeapChildOrder

/-- A strict heap-index comparison persists after appending
arbitrary equal-length direction sequences, even if they
differ in every direction. -/
theorem heapIndex_append_lt_of_lt_same_length {b : Nat}
    (s t u v : Node b)
    (hbase : heapIndex s < heapIndex t)
    (hlen : u.length = v.length) :
    heapIndex (s ++ u) < heapIndex (t ++ v) := by
  have hmain :
      ∀ (w : Node b) (s t v : Node b),
        heapIndex s < heapIndex t →
        w.length = v.length →
        heapIndex (s ++ w) < heapIndex (t ++ v) := by
    intro w
    induction w with
    | nil =>
        intro s t v hbase hlen
        cases v with
        | nil =>
            simpa using hbase
        | cons j tail =>
            simp at hlen
    | cons i tail ih =>
        intro s t v hbase hlen
        cases v with
        | nil =>
            simp at hlen
        | cons j vtail =>
            have htail : tail.length = vtail.length := by
              simpa using hlen
            have hchild :=
              heapIndex_child_lt_of_parent_lt s t i j hbase
            have hrest :=
              ih (s ++ [i]) (t ++ [j]) vtail hchild htail
            simpa [List.append_assoc] using hrest
  exact hmain u s t v hbase hlen

/-- Forward lexicographic order on two equal-length suffixes
implies monotonicity of their heap indices after any common
initial ambient prefix. -/
theorem heapIndex_append_le_of_same_length_lex {b : Nat}
    (base u v : Node b)
    (hlen : u.length = v.length)
    (hlex : FinLexLE u v) :
    heapIndex (base ++ u) ≤ heapIndex (base ++ v) := by
  have hmain :
      ∀ (w : Node b) (base v : Node b),
        w.length = v.length →
        FinLexLE w v →
        heapIndex (base ++ w) ≤ heapIndex (base ++ v) := by
    intro w
    induction w with
    | nil =>
        intro base v hlen _
        cases v with
        | nil =>
            simp
        | cons j tail =>
            simp at hlen
    | cons i tail ih =>
        intro base v hlen hlex
        cases v with
        | nil =>
            simp at hlen
        | cons j vtail =>
            have htail : tail.length = vtail.length := by
              simpa using hlen
            by_cases heq : i = j
            · subst j
              have hlexTail : FinLexLE tail vtail := by
                simpa [FinLexLE, finLexLEB] using hlex
              have hrec := ih (base ++ [i]) vtail htail hlexTail
              simpa [List.append_assoc] using hrec
            · have hij : i < j := by
                have h := hlex
                simp [FinLexLE, finLexLEB, heq] at h
                exact h
              have hfirst :=
                heapIndex_child_lt_of_direction_lt base i j hij
              have hsuf :=
                heapIndex_append_lt_of_lt_same_length
                  (base ++ [i]) (base ++ [j])
                  tail vtail hfirst htail
              have hlt :
                  heapIndex (base ++ (i :: tail)) <
                    heapIndex (base ++ (j :: vtail)) := by
                simpa [List.append_assoc] using hsuf
              exact Nat.le_of_lt hlt
  exact hmain u base v hlen hlex

/-- A pair of equal-length ambient model nodes in forward lex
order has nondecreasing arithmetic heap indices. -/
theorem heapIndex_le_of_same_length_lex {b : Nat}
    (s t : Node b)
    (hlen : s.length = t.length)
    (hlex : FinLexLE s t) :
    heapIndex s ≤ heapIndex t := by
  simpa using
    (heapIndex_append_le_of_same_length_lex
      ([] : Node b) s t hlen hlex)

/-- Strict heap-index comparison of equal-length addresses
implies their forward lexicographic ordering. No inverse
heap coding is presumed. -/
theorem finLexLE_of_heapIndex_lt_same_length {b : Nat}
    (s t : Node b)
    (hlen : s.length = t.length)
    (hindex : heapIndex s < heapIndex t) :
    FinLexLE s t := by
  rcases finLexLE_total s t with hst | hts
  · exact hst
  · have hle :=
      heapIndex_le_of_same_length_lex t s hlen.symm hts
    omega

end DualTree.ForwardModelHeapLexOrder
