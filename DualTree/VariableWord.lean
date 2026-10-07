import DualTree.SpanAudit
import DualTree.Basic

/-!
# Variable words indexed by finite homogeneous trees

This file formalizes the source-facing part of Sections 1.2 and 4.1 that is
independent of completeness/skewness of the support.

A variable word has:
* a finite list of support roots;
* one variable symbol for each support root;
* the variable occurring at its own root;
* every occurrence of that variable lying above its root.

The algebraic span is delegated to SpanAudit.  Combining the root condition
with the two-letter span/substitution theorem shows that span refinement also
preserves support roots.
-/

namespace DualTree

/-- A node of the finite homogeneous tree b^{<n}. -/
abbrev BoundedNode (b n : Nat) := {s : Node b // InHomTree n s}

/-- A constant word on b^{<n}. -/
abbrev TreeWord (b n : Nat) (α : Type*) := BoundedNode b n → α

structure VariableWord (b n : Nat) (α : Type*) where
  support : List (BoundedNode b n)
  support_nodup : support.Nodup
  word : BoundedNode b n → Sum α {t // t ∈ support}
  atRoot : ∀ v : {t // t ∈ support}, word v.1 = Sum.inr v
  below :
    ∀ (v : {t // t ∈ support}) (i : BoundedNode b n),
      word i = Sum.inr v → IsPrefix v.1.1 i.1

namespace VariableWord

abbrev Vars {b n : Nat} {α : Type*}
    (f : VariableWord b n α) := {t // t ∈ f.support}

def eval {b n : Nat} {α : Type*}
    (f : VariableWord b n α) (σ : f.Vars → α) :
    TreeWord b n α :=
  SpanAudit.eval f.word σ

def span {b n : Nat} {α : Type*}
    (f : VariableWord b n α) : Set (TreeWord b n α) :=
  SpanAudit.span f.word

theorem every_var_occurs {b n : Nat} {α : Type*}
    (f : VariableWord b n α) :
    ∀ v : f.Vars, ∃ i : BoundedNode b n, f.word i = Sum.inr v := by
  intro v
  exact ⟨v.1, f.atRoot v⟩

/--
For a nondegenerate alphabet, inclusion of evaluated spans is equivalent to a
uniform syntactic substitution between the tree-variable words.
-/
theorem span_subset_iff_substitution {b n : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f g : VariableWord b n α) :
    g.span ⊆ f.span ↔
      ∃ ρ : f.Vars → Sum α g.Vars,
        g.word = SpanAudit.substitute f.word ρ := by
  exact SpanAudit.span_subset_iff_substitution
    hα f.word g.word (every_var_occurs f)

/--
The root conditions upgrade algebraic substitution to support inclusion:
every variable root of a span-refinement is already a source variable root.
-/
theorem support_subset_of_span_subset {b n : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f g : VariableWord b n α)
    (hspan : g.span ⊆ f.span) :
    ∀ t, t ∈ g.support → t ∈ f.support := by
  intro t ht
  let v : g.Vars := ⟨t, ht⟩
  rcases (span_subset_iff_substitution hα f g).1 hspan with ⟨ρ, hword⟩
  have hgroot : g.word t = Sum.inr v := g.atRoot v
  have hsubroot :
      SpanAudit.substitute f.word ρ t = Sum.inr v := by
    rw [← hword]
    exact hgroot
  cases hft : f.word t with
  | inl a =>
      simp [SpanAudit.substitute, hft] at hsubroot
  | inr s =>
      have hrho : ρ s = Sum.inr v := by
        simpa [SpanAudit.substitute, hft] using hsubroot
      have ggAtS : g.word s.1 = Sum.inr v := by
        calc
          g.word s.1 =
              SpanAudit.substitute f.word ρ s.1 := congrFun hword s.1
          _ = ρ s := by
            simp [SpanAudit.substitute, f.atRoot s]
          _ = Sum.inr v := hrho
      have hst : IsPrefix s.1.1 t.1 :=
        f.below s t hft
      have hts : IsPrefix t.1 s.1.1 :=
        g.below v s.1 ggAtS
      have hnodes : s.1.1 = t.1 :=
        isPrefix_antisymm hst hts
      have hbounded : s.1 = t := by
        apply Subtype.ext
        exact hnodes
      rw [← hbounded]
      exact s.2

end VariableWord
end DualTree
