import DualTree.ForwardModelHeapLexOrder

/-!
# Disjoint arithmetic heap-index bands of homogeneous tree levels

At fixed branching b, the indices of nodes of a given ambient length
occupy one contiguous numerical interval. The lower and upper
endpoints of the length-n interval satisfy

  min(b,0)=max(b,0)=0
  min(b,n+1)=b*min(b,n)+1
  max(b,n+1)=b*max(b,n)+b
  max(b,n)+1=min(b,n+1).

A foldl induction proves every length-n direction list has heap
index between min(b,n) and max(b,n). For positive b the minimum
strictly increases in n. Therefore strictly shorter nodes have
strictly smaller heap indices, with no lex hypothesis needed.

Together with the equal-level forward lex comparisons proved in
ForwardModelHeapLexOrder, this establishes that the corrected
length-first forward auxiliary order is monotone under heapIndex.
Injectivity / full order reflection and the direction-preserving
canonical A-to-literal-R map remain separate obligations.
-/

namespace DualTree.ForwardModelHeapLevels

open ForwardModelBoundaryHeap
open ForwardModelHeapLexOrder

/-- Smallest breadth-first heap index at homogeneous level n. -/
def minIndex (b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => b * minIndex b n + 1

/-- Largest breadth-first heap index at homogeneous level n. -/
def maxIndex (b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => b * maxIndex b n + b

/-- Adjacent homogeneous-level index bands are consecutive:
the final index of one level is followed by the first of the next. -/
theorem maxIndex_succ_eq_minIndex (b n : Nat) :
    maxIndex b n + 1 = minIndex b (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        maxIndex b (n + 1) + 1 =
          b * maxIndex b n + b + 1 := rfl
        _ = b * (maxIndex b n + 1) + 1 := by
          simp [Nat.mul_add, Nat.add_assoc]
        _ = b * minIndex b (n + 1) + 1 := by rw [ih]
        _ = minIndex b (n + 2) := rfl

/-- The model heap fold preserves the bounds of homogeneous
levels for any partial prefix index and remaining suffix. -/
private theorem foldl_heap_bounds {b : Nat} :
    ∀ (s : Node b) (q n : Nat),
      minIndex b n ≤ q →
      q ≤ maxIndex b n →
      minIndex b (n + s.length) ≤
        s.foldl (fun q i => b * q + 1 + i.val) q ∧
      s.foldl (fun q i => b * q + 1 + i.val) q ≤
        maxIndex b (n + s.length) := by
  intro s
  induction s with
  | nil =>
      intro q n hl hu
      simpa using (And.intro hl hu)
  | cons i tail ih =>
      intro q n hl hu
      have hmulLo : b * minIndex b n ≤ b * q :=
        Nat.mul_le_mul_left b hl
      have hmulHi : b * q ≤ b * maxIndex b n :=
        Nat.mul_le_mul_left b hu
      have hdir : i.val < b := i.isLt
      have hl' : minIndex b (n + 1) ≤ b * q + 1 + i.val := by
        change b * minIndex b n + 1 ≤ b * q + 1 + i.val
        omega
      have hu' : b * q + 1 + i.val ≤ maxIndex b (n + 1) := by
        change b * q + 1 + i.val ≤ b * maxIndex b n + b
        omega
      have hr := ih (b * q + 1 + i.val) (n + 1) hl' hu'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

/-- Any ambient level-n node lies in the exact numerical
level-n heap band. No positive-b assumption is required. -/
theorem heapIndex_level_bounds {b : Nat} (s : Node b) :
    minIndex b s.length ≤ heapIndex s ∧
    heapIndex s ≤ maxIndex b s.length := by
  have h := foldl_heap_bounds s 0 0 (by simp [minIndex]) (by simp [maxIndex])
  simpa [heapIndex] using h

/-- For positive branching, the first index of every level
is strictly below the first index of the next level. -/
theorem minIndex_lt_succ {b : Nat}
    (hb : 0 < b) (n : Nat) :
    minIndex b n < minIndex b (n + 1) := by
  have hmul : minIndex b n ≤ b * minIndex b n := by
    have hb1 : 1 ≤ b := by omega
    calc
      minIndex b n = 1 * minIndex b n := by simp
      _ ≤ b * minIndex b n :=
        Nat.mul_le_mul_right (minIndex b n) hb1
  change minIndex b n < b * minIndex b n + 1
  omega

/-- The lower endpoint of the heap band is monotone in
homogeneous level for positive branching. -/
theorem minIndex_mono {b : Nat}
    (hb : 0 < b) {n m : Nat} (hnm : n ≤ m) :
    minIndex b n ≤ minIndex b m := by
  have haux : ∀ d : Nat, minIndex b n ≤ minIndex b (n + d) := by
    intro d
    induction d with
    | zero =>
        simp
    | succ d ih =>
        calc
          minIndex b n ≤ minIndex b (n + d) := ih
          _ ≤ minIndex b ((n + d) + 1) :=
            Nat.le_of_lt (minIndex_lt_succ hb (n + d))
          _ = minIndex b (n + (d + 1)) := by
            congr 1
            omega
  have h := haux (m - n)
  rwa [Nat.add_sub_of_le hnm] at h

/-- Different homogeneous levels have disjoint ordered
heap-index bands. This is the length comparison half of
the corrected forward auxiliary order. -/
theorem heapIndex_lt_of_length_lt {b : Nat}
    (hb : 0 < b)
    (s t : Node b)
    (hlen : s.length < t.length) :
    heapIndex s < heapIndex t := by
  have hs := heapIndex_level_bounds s
  have ht := heapIndex_level_bounds t
  have hband := maxIndex_succ_eq_minIndex b s.length
  have hmono : minIndex b (s.length + 1) ≤ minIndex b t.length :=
    minIndex_mono hb (Nat.succ_le_of_lt hlen)
  omega

/-- The corrected forward auxiliary order is monotone under
the arithmetic heap index on the entire homogeneous tree,
not merely within a fixed level. -/
theorem heapIndex_mono_of_forwardAux {b : Nat}
    (hb : 0 < b)
    (s t : Node b)
    (hst : ForwardAux s t) :
    heapIndex s ≤ heapIndex t := by
  rcases hst with hlen | ⟨hlen, hlex⟩
  · exact Nat.le_of_lt (heapIndex_lt_of_length_lt hb s t hlen)
  · exact heapIndex_le_of_same_length_lex s t hlen hlex

end DualTree.ForwardModelHeapLevels
