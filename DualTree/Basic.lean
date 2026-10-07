import Mathlib

/-!
# Basic finite-tree language for the Todorcevic--Tyros audit

This file deliberately starts below the paper's skew-tree notions.  Nodes of the
homogeneous `b`-ary tree are finite lists over `Fin b`; bounded trees are
represented by a length predicate.  We use an explicit prefix predicate rather
than importing an order convention, because one of the first audited issues in
the paper concerns a separate linear order on nodes.
-/

namespace DualTree

/-- A node of the homogeneous `b`-ary tree. -/
abbrev Node (b : Nat) := List (Fin b)

/-- Membership in the finite tree `b^{<n}`. -/
def InHomTree {b : Nat} (n : Nat) (s : Node b) : Prop :=
  s.length < n

/-- Initial-segment relation, written explicitly as concatenation by a tail. -/
def IsPrefix {b : Nat} (s t : Node b) : Prop :=
  ∃ u, t = s ++ u

/-- Proper initial segment. -/
def IsStrictPrefix {b : Nat} (s t : Node b) : Prop :=
  IsPrefix s t ∧ s ≠ t

theorem isPrefix_refl {b : Nat} (s : Node b) : IsPrefix s s := by
  refine ⟨[], ?_⟩
  simp

theorem isPrefix_trans {b : Nat} {r s t : Node b}
    (hrs : IsPrefix r s) (hst : IsPrefix s t) : IsPrefix r t := by
  rcases hrs with ⟨u, rfl⟩
  rcases hst with ⟨v, rfl⟩
  refine ⟨u ++ v, ?_⟩
  simp [List.append_assoc]

theorem prefix_length_le {b : Nat} {s t : Node b}
    (h : IsPrefix s t) : s.length ≤ t.length := by
  rcases h with ⟨u, rfl⟩
  simp


theorem isPrefix_antisymm {b : Nat} {s t : Node b}
    (hst : IsPrefix s t) (hts : IsPrefix t s) : s = t := by
  rcases hst with ⟨u, rfl⟩
  have hlen := prefix_length_le hts
  have hu : u.length = 0 := by
    simp only [List.length_append] at hlen
    omega
  cases u with
  | nil => simp
  | cons a u =>
      simp at hu

end DualTree
