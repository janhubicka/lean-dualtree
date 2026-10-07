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
  exact f.support_nodup.map (fun x y hxy => Subtype.ext hxy)

end VariableWord

/--
A source-facing k-variable word with complete skew support.
-/
structure KVariableWord
    (b n k : Nat) (α : Type*)
    (aux : Node b → Node b → Bool) where
  toVariableWord : VariableWord b n α
  complete_support :
    SkewTree.completeB aux k toVariableWord.supportNodes = true

namespace KVariableWord

variable {aux : Node b → Node b → Bool}
variable {k k' b n : Nat} {α : Type*}

abbrev support
    (f : KVariableWord b n k α aux) :=
  f.toVariableWord.support

abbrev word
    (f : KVariableWord b n k α aux) :=
  f.toVariableWord.word

abbrev span
    (f : KVariableWord b n k α aux) :=
  f.toVariableWord.span

abbrev Vars
    (f : KVariableWord b n k α aux) :=
  f.toVariableWord.Vars

/-- Evaluated-span refinement, exactly as used in the paper. -/
def Refines
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux) : Prop :=
  g.span ⊆ f.span

/-- Uniform syntactic substitution refinement. -/
def SyntacticRefines
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux) : Prop :=
  ∃ ρ : f.Vars → Sum α g.Vars,
    g.word = SpanAudit.substitute f.word ρ

theorem refines_refl
    (f : KVariableWord b n k α aux) :
    Refines f f := by
  intro x hx
  exact hx

theorem refines_trans
    {k'' : Nat}
    (h : KVariableWord b n k'' α aux)
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux)
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
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux) :
    Refines g f ↔ SyntacticRefines g f := by
  exact VariableWord.span_subset_iff_substitution
    hα f.toVariableWord g.toVariableWord

/--
Span refinement over a nondegenerate alphabet preserves variable roots.
-/
theorem support_subset_of_refines
    (hα : SpanAudit.HasTwoLetters α)
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux)
    (hgf : Refines g f) :
    ∀ t, t ∈ g.support → t ∈ f.support := by
  exact VariableWord.support_subset_of_span_subset
    hα f.toVariableWord g.toVariableWord hgf

end KVariableWord

/-- k-variable words using the order literally printed in the paper. -/
abbrev PaperKVariableWord
    (k b n : Nat) (α : Type*) :=
  KVariableWord b n k α (SkewTree.paperAuxB (b := b))

/-- k-variable words using the candidate forward-lex repair. -/
abbrev ForwardKVariableWord
    (k b n : Nat) (α : Type*) :=
  KVariableWord b n k α (SkewTree.forwardAuxB (b := b))

end DualTree
