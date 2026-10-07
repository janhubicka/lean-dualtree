import DualTree.VariableWord
import DualTree.SkewTree

/-!
# Complete-support variable words

This file packages the paper-level notion of a k-variable word: a tree-indexed
variable word whose set of variable roots is a k-complete skew subtree.

The auxiliary order is kept as an explicit parameter.  Thus the same API can
be used both for the printed reverse-lex convention and for the forward-lex
repair adopted in the structural audit.
-/

namespace DualTree

namespace VariableWord

/-- Forget the ambient-height proofs on the support roots. -/
def supportNodes {b n : Nat} {α : Type*}
    (f : VariableWord b n α) : List (Node b) :=
  f.support.map (fun t => t.1)

theorem supportNodes_nodup {b n : Nat} {α : Type*}
    (f : VariableWord b n α) :
    (supportNodes f).Nodup := by
  apply List.Nodup.map
  · intro x hx y hy hxy
    apply Subtype.ext
    exact hxy
  · exact f.support_nodup

end VariableWord

/--
A source-facing k-variable word with complete skew support.
-/
structure KVariableWord
    (aux : Node b → Node b → Bool)
    (k b n : Nat) (α : Type*) where
  toVariableWord : VariableWord b n α
  complete_support :
    SkewTree.completeB aux k toVariableWord.supportNodes = true

namespace KVariableWord

variable {aux : Node b → Node b → Bool}
variable {k k' b n : Nat} {α : Type*}

abbrev support
    (f : KVariableWord aux k b n α) :=
  f.toVariableWord.support

abbrev word
    (f : KVariableWord aux k b n α) :=
  f.toVariableWord.word

abbrev span
    (f : KVariableWord aux k b n α) :=
  f.toVariableWord.span

abbrev Vars
    (f : KVariableWord aux k b n α) :=
  f.toVariableWord.Vars

/-- Evaluated-span refinement, exactly as used in the paper. -/
def Refines
    (g : KVariableWord aux k' b n α)
    (f : KVariableWord aux k b n α) : Prop :=
  g.span ⊆ f.span

/-- Uniform syntactic substitution refinement. -/
def SyntacticRefines
    (g : KVariableWord aux k' b n α)
    (f : KVariableWord aux k b n α) : Prop :=
  ∃ ρ : f.Vars → Sum α g.Vars,
    g.word = SpanAudit.substitute f.word ρ

theorem refines_refl
    (f : KVariableWord aux k b n α) :
    Refines f f := by
  intro x hx
  exact hx

theorem refines_trans
    {k'' : Nat}
    (h : KVariableWord aux k'' b n α)
    (g : KVariableWord aux k' b n α)
    (f : KVariableWord aux k b n α)
    (hhg : Refines h g)
    (hgf : Refines g f) :
    Refines h f := by
  intro x hx
  exact hgf (hhg hx)

/--
For a nondegenerate alphabet, the paper's evaluated-span refinement is exactly
uniform syntactic substitution.
-/
theorem refines_iff_syntactic
    (hα : SpanAudit.HasTwoLetters α)
    (g : KVariableWord aux k' b n α)
    (f : KVariableWord aux k b n α) :
    Refines g f ↔ SyntacticRefines g f := by
  exact VariableWord.span_subset_iff_substitution
    hα f.toVariableWord g.toVariableWord

/--
Span refinement over a nondegenerate alphabet preserves variable roots.
-/
theorem support_subset_of_refines
    (hα : SpanAudit.HasTwoLetters α)
    (g : KVariableWord aux k' b n α)
    (f : KVariableWord aux k b n α)
    (hgf : Refines g f) :
    ∀ t, t ∈ g.support → t ∈ f.support := by
  exact VariableWord.support_subset_of_span_subset
    hα f.toVariableWord g.toVariableWord hgf

end KVariableWord

/-- k-variable words using the order literally printed in the paper. -/
abbrev PaperKVariableWord
    (k b n : Nat) (α : Type*) :=
  KVariableWord (SkewTree.paperAuxB (b := b)) k b n α

/-- k-variable words using the candidate forward-lex repair. -/
abbrev ForwardKVariableWord
    (k b n : Nat) (α : Type*) :=
  KVariableWord (SkewTree.forwardAuxB (b := b)) k b n α

end DualTree
