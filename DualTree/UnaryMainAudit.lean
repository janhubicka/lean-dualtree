import DualTree.VariableWord
import DualTree.SkewTree

/-!
# Unary-alphabet counterexample to the literal main theorem

The paper defines refinement by inclusion of evaluated spans.  Over a
one-letter alphabet this relation is universal, so a candidate cannot restrict
the location of a one-node variable support.

This file turns that observation into the paper's tree-variable language.  For
every binary ambient height n >= 2 we exhibit two 1-complete variable words,
one rooted at the tree root and one rooted at its left child.  Both refine
every candidate over PUnit, but a fixed coloring distinguishes them.  Hence no
eventual threshold can satisfy the literal l = 1, k = m = 1 instance of
Theorem 3.
-/

namespace DualTree.UnaryMainAudit

open VariableWord
open SkewTree

def root2 (n : Nat) (hn : 2 ≤ n) : BoundedNode 2 n :=
  ⟨[], by
    simp [InHomTree]
    omega⟩

def left2 (n : Nat) (hn : 2 ≤ n) : BoundedNode 2 n :=
  ⟨[0], by
    simp [InHomTree]
    omega⟩

theorem root2_ne_left2 (n : Nat) (hn : 2 ≤ n) :
    root2 n hn ≠ left2 n hn := by
  intro h
  have hv := congrArg Subtype.val h
  simp [root2, left2] at hv

/-- The simplest variable word: one variable occurring only at its root. -/
def singletonVariableWord {b n : Nat} {α : Type*}
    (r : BoundedNode b n) (a : α) : VariableWord b n α where
  support := [r]
  support_nodup := by simp
  word := fun i =>
    if h : i = r then
      Sum.inr ⟨r, by simp⟩
    else
      Sum.inl a
  atRoot := by
    rintro ⟨t, ht⟩
    have htr : t = r := by simpa using ht
    subst t
    simp
  below := by
    rintro ⟨t, ht⟩ i hword
    have htr : t = r := by simpa using ht
    subst t
    by_cases hir : i = r
    · subst i
      exact isPrefix_refl r.1
    · simp [hir] at hword

def rootWord (n : Nat) (hn : 2 ≤ n) : VariableWord 2 n PUnit :=
  singletonVariableWord (root2 n hn) PUnit.unit

def leftWord (n : Nat) (hn : 2 ≤ n) : VariableWord 2 n PUnit :=
  singletonVariableWord (left2 n hn) PUnit.unit

def supportNodes {b n : Nat} {α : Type*}
    (f : VariableWord b n α) : List (Node b) :=
  f.support.map Subtype.val

def CompleteSupport {b n : Nat} {α : Type*}
    (aux : Node b → Node b → Bool) (k : Nat)
    (f : VariableWord b n α) : Prop :=
  SkewTree.Complete aux k (supportNodes f)

def Refines {b n : Nat} {α : Type*}
    (g f : VariableWord b n α) : Prop :=
  g.span ⊆ f.span

/-- Over PUnit every tree-variable word refines every other one. -/
theorem unary_refines_all {b n : Nat}
    (g f : VariableWord b n PUnit) :
    Refines g f := by
  exact SpanAudit.singleton_span_subset g.word f.word

theorem rootWord_complete (n : Nat) (hn : 2 ≤ n) :
    CompleteSupport forwardAuxB 1 (rootWord n hn) := by
  simp [CompleteSupport, supportNodes, rootWord, singletonVariableWord,
    SkewTree.Complete]
  exact SkewTree.singleton_complete_oneB forwardAuxB []

theorem leftWord_complete (n : Nat) (hn : 2 ≤ n) :
    CompleteSupport forwardAuxB 1 (leftWord n hn) := by
  simp [CompleteSupport, supportNodes, leftWord, singletonVariableWord,
    SkewTree.Complete]
  exact SkewTree.singleton_complete_oneB forwardAuxB [0]

/-- Fixed two-coloring used in the counterexample. -/
def rootColor (n : Nat) (hn : 2 ≤ n)
    (f : VariableWord 2 n PUnit) : Bool :=
  decide (root2 n hn ∈ f.support)

theorem rootColor_rootWord (n : Nat) (hn : 2 ≤ n) :
    rootColor n hn (rootWord n hn) = true := by
  simp [rootColor, rootWord, singletonVariableWord]

theorem rootColor_leftWord (n : Nat) (hn : 2 ≤ n) :
    rootColor n hn (leftWord n hn) = false := by
  simp [rootColor, leftWord, singletonVariableWord, root2_ne_left2 n hn]

/-- Homogeneity of all 1-complete refinements for the fixed root coloring. -/
def HomogeneousOne (n : Nat) (hn : 2 ≤ n)
    (f : VariableWord 2 n PUnit) : Prop :=
  ∃ c : Bool,
    ∀ g : VariableWord 2 n PUnit,
      CompleteSupport forwardAuxB 1 g →
      Refines g f →
      rootColor n hn g = c

/-- No candidate has homogeneous 1-complete refinements for this coloring. -/
theorem no_homogeneous_one (n : Nat) (hn : 2 ≤ n)
    (f : VariableWord 2 n PUnit) :
    ¬ HomogeneousOne n hn f := by
  rintro ⟨c, hc⟩
  have hroot := hc (rootWord n hn) (rootWord_complete n hn)
    (unary_refines_all _ f)
  have hleft := hc (leftWord n hn) (leftWord_complete n hn)
    (unary_refines_all _ f)
  rw [rootColor_rootWord] at hroot
  rw [rootColor_leftWord] at hleft
  cases c <;> simp at hroot hleft

/--
There is no eventual ambient-height bound making the literal unary instance
Ramsey.  This is the threshold-level contradiction needed for Theorem 3, not
merely a counterexample at one small height.
-/
theorem no_unary_eventual_bound :
    ¬ ∃ n0 : Nat,
      ∀ n : Nat, ∀ hn : 2 ≤ n, n0 < n →
        ∃ f : VariableWord 2 n PUnit,
          CompleteSupport forwardAuxB 1 f ∧
          HomogeneousOne n hn f := by
  rintro ⟨n0, h⟩
  let n := n0 + 2
  have hn : 2 ≤ n := by
    simp [n]
  have hgt : n0 < n := by
    simp [n]
  rcases h n hn hgt with ⟨f, _, hf⟩
  exact no_homogeneous_one n hn f hf

end DualTree.UnaryMainAudit
