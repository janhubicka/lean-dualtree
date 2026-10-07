import DualTree.KVariableWord

/-!
# Preservation of the initial segment in Definition 26

The observation immediately after Definition 26 asserts that a syntactic
refinement which retains every support root up to t0 leaves the word unchanged
up to t0. The paper compares variable symbols by their underlying roots;
Lean must erase the support-dependent subtype proofs before doing so.

Both the printed reverse-lex order and the candidate forward-lex repair are
handled. Span containment justifies the syntactic refinement hypothesis only
when the alphabet contains two distinct letters (the unary counterexample
was formalized earlier).

These lemmas do not yet prove invariance of the full set of observable
signatures; that also requires the geometric signature construction.
-/

namespace DualTree.CutPreservation

/-- An initial segment of the same length is the whole word. -/
theorem prefix_eq_of_length_eq {b : Nat} {r s : Node b}
    (hrs : IsPrefix r s) (hlen : r.length = s.length) : r = s := by
  rcases hrs with ⟨u, rfl⟩
  have hu : u.length = 0 := by
    simp only [List.length_append] at hlen
    omega
  cases u with
  | nil => simp
  | cons x xs => simp at hu

/--
Every length-first auxiliary order is monotone in its first argument when
that argument is replaced by a prefix. The tie-break need not be specified.
-/
theorem lengthTie_of_prefix {b : Nat}
    (tie : Node b → Node b → Prop)
    {r s t : Node b}
    (hrs : IsPrefix r s)
    (hst : s.length < t.length ∨
      (s.length = t.length ∧ tie s t)) :
    r.length < t.length ∨
      (r.length = t.length ∧ tie r t) := by
  have hlen : r.length ≤ s.length := prefix_length_le hrs
  rcases hst with hlt | ⟨heq, htie⟩
  · exact Or.inl (lt_of_le_of_lt hlen hlt)
  · by_cases hlt : r.length < s.length
    · exact Or.inl (by omega)
    · have hsame : r.length = s.length := by omega
      have hrsEq : r = s := prefix_eq_of_length_eq hrs hsame
      subst r
      exact Or.inr ⟨heq, htie⟩

theorem paperAux_of_prefix {b : Nat} {r s t : Node b}
    (hrs : IsPrefix r s) (hst : PaperAux s t) :
    PaperAux r t :=
  lengthTie_of_prefix (fun x y => FinLexLE y x) hrs hst

theorem forwardAux_of_prefix {b : Nat} {r s t : Node b}
    (hrs : IsPrefix r s) (hst : ForwardAux s t) :
    ForwardAux r t :=
  lengthTie_of_prefix (fun x y => FinLexLE x y) hrs hst

/--
Expose a variable symbol by its actual root rather than by a subtype
membership proof, which differs between source and refined word.
-/
def underlyingSymbol {b n : Nat} {α : Type*}
    (f : VariableWord b n α) (s : BoundedNode b n) :
    Sum α (BoundedNode b n) :=
  match f.word s with
  | Sum.inl a => Sum.inl a
  | Sum.inr v => Sum.inr v.1

/--
Uniform syntactic refinement plus retention of all support roots at or
before the cut preserves every letter or rooted variable symbol in the
ambient initial segment.
-/
theorem underlyingSymbol_eq_of_syntactic_cut
    {b n : Nat} {α : Type*}
    (R : Node b → Node b → Prop)
    (hprefix : ∀ {r s t : Node b},
      IsPrefix r s → R s t → R r t)
    (f g : VariableWord b n α)
    (ρ : f.Vars → Sum α g.Vars)
    (hword : g.word = SpanAudit.substitute f.word ρ)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      R r.1 cut.1 → r ∈ g.support)
    (s : BoundedNode b n)
    (hs : R s.1 cut.1) :
    underlyingSymbol g s = underlyingSymbol f s := by
  classical
  cases hfs : f.word s with
  | inl a =>
      have hgs : g.word s = Sum.inl a := by
        calc
          g.word s = SpanAudit.substitute f.word ρ s :=
            congrFun hword s
          _ = Sum.inl a := by
            simp [SpanAudit.substitute, hfs]
      simp [underlyingSymbol, hfs, hgs]
  | inr v =>
      have hcut : R v.1.1 cut.1 :=
        hprefix (f.below v s hfs) hs
      have hv : v.1 ∈ g.support :=
        hkeep v.1 v.2 hcut
      let w : g.Vars := ⟨v.1, hv⟩
      have hwroot : g.word v.1 = Sum.inr w := g.atRoot w
      have hρ : ρ v = Sum.inr w := by
        calc
          ρ v = SpanAudit.substitute f.word ρ v.1 := by
            simp [SpanAudit.substitute, f.atRoot v]
          _ = g.word v.1 := (congrFun hword v.1).symm
          _ = Sum.inr w := hwroot
      have hgs : g.word s = Sum.inr w := by
        calc
          g.word s = SpanAudit.substitute f.word ρ s :=
            congrFun hword s
          _ = ρ v := by
            simp [SpanAudit.substitute, hfs]
          _ = Sum.inr w := hρ
      simp [underlyingSymbol, hfs, hgs, w]

/-- Definition 26 prefix preservation for the auxiliary order as printed. -/
theorem paperCut_preserved_of_syntactic_refinement
    {b n : Nat} {α : Type*}
    (f g : VariableWord b n α)
    (ρ : f.Vars → Sum α g.Vars)
    (hword : g.word = SpanAudit.substitute f.word ρ)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      PaperAux r.1 cut.1 → r ∈ g.support)
    (s : BoundedNode b n)
    (hs : PaperAux s.1 cut.1) :
    underlyingSymbol g s = underlyingSymbol f s :=
  underlyingSymbol_eq_of_syntactic_cut
    PaperAux (fun _ _ _ hp h => paperAux_of_prefix hp h)
    f g ρ hword cut hkeep s hs

/-- The same assertion for the repaired forward-lex auxiliary order. -/
theorem forwardCut_preserved_of_syntactic_refinement
    {b n : Nat} {α : Type*}
    (f g : VariableWord b n α)
    (ρ : f.Vars → Sum α g.Vars)
    (hword : g.word = SpanAudit.substitute f.word ρ)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      ForwardAux r.1 cut.1 → r ∈ g.support)
    (s : BoundedNode b n)
    (hs : ForwardAux s.1 cut.1) :
    underlyingSymbol g s = underlyingSymbol f s :=
  underlyingSymbol_eq_of_syntactic_cut
    ForwardAux (fun _ _ _ hp h => forwardAux_of_prefix hp h)
    f g ρ hword cut hkeep s hs

/--
If the alphabet has two distinct letters, the paper's span-inclusion
refinement implies the same initial-segment equality.
-/
theorem paperCut_preserved_of_span_refinement
    {b n : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f g : VariableWord b n α)
    (hspan : g.span ⊆ f.span)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      PaperAux r.1 cut.1 → r ∈ g.support)
    (s : BoundedNode b n)
    (hs : PaperAux s.1 cut.1) :
    underlyingSymbol g s = underlyingSymbol f s := by
  rcases (VariableWord.span_subset_iff_substitution hα f g).1
      hspan with ⟨ρ, hword⟩
  exact paperCut_preserved_of_syntactic_refinement
    f g ρ hword cut hkeep s hs

/-- Span-based prefix preservation under the candidate forward-lex repair. -/
theorem forwardCut_preserved_of_span_refinement
    {b n : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f g : VariableWord b n α)
    (hspan : g.span ⊆ f.span)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      ForwardAux r.1 cut.1 → r ∈ g.support)
    (s : BoundedNode b n)
    (hs : ForwardAux s.1 cut.1) :
    underlyingSymbol g s = underlyingSymbol f s := by
  rcases (VariableWord.span_subset_iff_substitution hα f g).1
      hspan with ⟨ρ, hword⟩
  exact forwardCut_preserved_of_syntactic_refinement
    f g ρ hword cut hkeep s hs

end DualTree.CutPreservation
