import DualTree.VariableWord
import DualTree.SkewTree

/-!
# Unary-alphabet tree counterexample

This file upgrades the abstract singleton-alphabet span collapse to the actual
tree-variable-word language used in Theorem 3.

For b = 2 and n = 2 we construct two one-variable words:
* one rooted at the empty node;
* one rooted at the left child.

Their singleton supports are 1-complete skew trees, their evaluated spans over
PUnit are identical, but the supports are different.  Hence the coloring
"does the variable support contain the root?" takes both colors below every
candidate when refinement is defined only by evaluated-span inclusion.
-/

namespace DualTree.Theorem3Audit

open VariableWord

def root : BoundedNode 2 2 :=
  ⟨[], by decide⟩

def left : BoundedNode 2 2 :=
  ⟨[(0 : Fin 2)], by decide⟩

def rootVar : {t // t ∈ [root]} :=
  ⟨root, by simp⟩

def leftVar : {t // t ∈ [left]} :=
  ⟨left, by simp⟩

def rootWord : VariableWord 2 2 PUnit where
  support := [root]
  support_nodup := by simp
  word := fun _ => Sum.inr rootVar
  atRoot := by
    intro v
    have hv : v.1 = root := by simpa using v.2
    have hsub : v = rootVar := by
      apply Subtype.ext
      exact hv
    subst v
    rfl
  below := by
    intro v i h
    have hv : rootVar = v := Sum.inr.inj h
    subst v
    refine ⟨i.1, ?_⟩
    simp [root]

def leftWord : VariableWord 2 2 PUnit where
  support := [left]
  support_nodup := by simp
  word := fun i =>
    if h : i = left then Sum.inr leftVar else Sum.inl PUnit.unit
  atRoot := by
    intro v
    have hv : v.1 = left := by simpa using v.2
    have hsub : v = leftVar := by
      apply Subtype.ext
      exact hv
    subst v
    simp [leftVar]
  below := by
    intro v i h
    by_cases hi : i = left
    · subst i
      exact isPrefix_refl _
    · simp [hi] at h

def supportNodes {b n : Nat} {α : Type*}
    (f : VariableWord b n α) : List (Node b) :=
  f.support.map (fun t => t.1)

theorem root_ne_left : root ≠ left := by
  decide

theorem root_support_complete :
    SkewTree.completeB SkewTree.paperAuxB 1 (supportNodes rootWord) = true := by
  simpa [supportNodes, rootWord] using
    (SkewTree.singleton_complete_oneB SkewTree.paperAuxB root.1)

theorem left_support_complete :
    SkewTree.completeB SkewTree.paperAuxB 1 (supportNodes leftWord) = true := by
  simpa [supportNodes, leftWord] using
    (SkewTree.singleton_complete_oneB SkewTree.paperAuxB left.1)

theorem supports_differ :
    rootWord.support ≠ leftWord.support := by
  simp [rootWord, leftWord, root_ne_left]

theorem unary_spans_equal :
    rootWord.span = leftWord.span := by
  unfold VariableWord.span
  exact SpanAudit.singleton_span_eq rootWord.word leftWord.word

/-- The paper's span-inclusion refinement makes both witnesses refinements of
every unary-alphabet candidate. -/
theorem both_refine_every_candidate (f : VariableWord 2 2 PUnit) :
    rootWord.span ⊆ f.span ∧ leftWord.span ⊆ f.span := by
  constructor
  · exact SpanAudit.singleton_span_subset rootWord.word f.word
  · exact SpanAudit.singleton_span_subset leftWord.word f.word

/-- Two-coloring used in the literal unary-alphabet counterexample. -/
def rootColor (f : VariableWord 2 2 PUnit) : Bool :=
  decide (root ∈ f.support)

theorem rootColor_rootWord : rootColor rootWord = true := by
  simp [rootColor, rootWord]

theorem rootColor_leftWord : rootColor leftWord = false := by
  simp [rootColor, leftWord, root_ne_left]

/--
Every candidate contains refinements of both colors under the paper's literal
span-inclusion definition.  Together with the two completeness lemmas above,
this is the finite mechanism refuting Theorem 3 for ell = 1.
-/
theorem two_colors_below_every_candidate (f : VariableWord 2 2 PUnit) :
    rootWord.span ⊆ f.span ∧
    leftWord.span ⊆ f.span ∧
    rootColor rootWord ≠ rootColor leftWord := by
  rcases both_refine_every_candidate f with ⟨hroot, hleft⟩
  refine ⟨hroot, hleft, ?_⟩
  simp [rootColor_rootWord, rootColor_leftWord]

end DualTree.Theorem3Audit
