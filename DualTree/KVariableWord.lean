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

variable {b n k k' : Nat} {α : Type*}
variable {aux : Node b → Node b → Bool}

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

/-- Extend a substitution to constant-or-variable symbols. -/
def mapSymbol {β γ : Type*}
    (ρ : β → Sum α γ) : Sum α β → Sum α γ
  | Sum.inl a => Sum.inl a
  | Sum.inr v => ρ v

theorem substitute_compose {ι β γ δ : Type*}
    (w : ι → Sum α β)
    (ρ₁ : β → Sum α γ)
    (ρ₂ : γ → Sum α δ) :
    SpanAudit.substitute (SpanAudit.substitute w ρ₁) ρ₂ =
      SpanAudit.substitute w (fun v => mapSymbol ρ₂ (ρ₁ v)) := by
  funext i
  cases hwi : w i with
  | inl a =>
      simp [SpanAudit.substitute, hwi]
  | inr v =>
      cases hv : ρ₁ v with
      | inl a =>
          simp [SpanAudit.substitute, hwi, hv, mapSymbol]
      | inr u =>
          simp [SpanAudit.substitute, hwi, hv, mapSymbol]

theorem syntacticRefines_refl
    (f : KVariableWord b n k α aux) :
    SyntacticRefines f f := by
  refine ⟨fun v => Sum.inr v, ?_⟩
  funext i
  cases hwi : f.word i with
  | inl a =>
      simp [SpanAudit.substitute, hwi]
  | inr v =>
      simp [SpanAudit.substitute, hwi]

theorem syntacticRefines_trans
    {k'' : Nat}
    (h : KVariableWord b n k'' α aux)
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux)
    (hhg : SyntacticRefines h g)
    (hgf : SyntacticRefines g f) :
    SyntacticRefines h f := by
  rcases hhg with ⟨ρhg, hh⟩
  rcases hgf with ⟨ρgf, hg⟩
  refine ⟨fun v => mapSymbol ρhg (ρgf v), ?_⟩
  calc
    h.word = SpanAudit.substitute g.word ρhg := hh
    _ = SpanAudit.substitute (SpanAudit.substitute f.word ρgf) ρhg := by rw [hg]
    _ = SpanAudit.substitute f.word (fun v => mapSymbol ρhg (ρgf v)) :=
      substitute_compose f.word ρgf ρhg

theorem syntacticRefines_refines
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux)
    (hgf : SyntacticRefines g f) :
    Refines g f := by
  rcases hgf with ⟨ρ, hg⟩
  change SpanAudit.span g.word ⊆ SpanAudit.span f.word
  rw [hg]
  exact SpanAudit.span_substitute_subset f.word ρ

/--
Syntactic refinement preserves variable roots for every alphabet, including
the unary case.
-/
theorem support_subset_of_syntacticRefines
    (g : KVariableWord b n k' α aux)
    (f : KVariableWord b n k α aux)
    (hgf : SyntacticRefines g f) :
    ∀ t, t ∈ g.support → t ∈ f.support := by
  intro t ht
  let v : g.Vars := ⟨t, ht⟩
  rcases hgf with ⟨ρ, hword⟩
  have hgroot : g.word t = Sum.inr v := g.toVariableWord.atRoot v
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
            simp [SpanAudit.substitute, f.toVariableWord.atRoot s]
          _ = Sum.inr v := hrho
      have hst : IsPrefix s.1.1 t.1 :=
        f.toVariableWord.below s t hft
      have hts : IsPrefix t.1 s.1.1 :=
        g.toVariableWord.below v s.1 ggAtS
      have hnodes : s.1.1 = t.1 :=
        isPrefix_antisymm hst hts
      have hbounded : s.1 = t := by
        apply Subtype.ext
        exact hnodes
      rw [← hbounded]
      exact s.2

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
