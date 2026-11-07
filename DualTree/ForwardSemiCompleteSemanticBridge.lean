import DualTree.ForwardSemiCompleteSimplicity

/-!
# Semantic-colour and syntactic-refinement bridge for Definition 24

This connects Track E's source-independent, span-based simplicity predicate
with the semantic-observation, syntactic-refinement convention used by the
corrected theorem specifications.

The forward implication requires no alphabet hypothesis: a syntactic
refinement is a span refinement. The converse explicitly requires
SpanAudit.HasTwoLetters; in particular no false unary span-to-syntactic
equivalence is asserted. The common-root word labels are definitionally
the underlying symbols of the semantic observation.

This file proves the equivalence of the *simplicity hypotheses*. It does
not assume that arbitrary Q outputs satisfy syntactic refinement, claim
a new relative Ramsey theorem, or discharge the coverage input of the
Theorem 25 induction.
-/

namespace DualTree.ForwardSemiCompleteSemanticBridge

open ForwardSemiCompleteSimplicity

/-- The semantic observation ignores support-list presentation and variable
membership proofs; it agrees definitionally with the corrected source
specification's starred-observation type. -/
abbrev SemanticObservation (b n : Nat) (α : Type*) :=
  Finset (Node b) × (BoundedNode b n → Sum α (BoundedNode b n))

noncomputable def observe
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    SemanticObservation b n α := by
  classical
  exact (U.tree.toFinset, CutPreservation.underlyingSymbol U.word)

/-- Track E's root label is the underlying symbol used in the source-facing
semantic observation. No injectivity assumption on a decoder is needed. -/
theorem rootLabel_eq_underlyingSymbol
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (s : BoundedNode b n) :
    ForwardQSimpleLetterSmooth.rootLabel U s =
      CutPreservation.underlyingSymbol U.word s := by
  cases h : U.word.word s with
  | inl a =>
      simp [ForwardQSimpleLetterSmooth.rootLabel,
        CutPreservation.underlyingSymbol, h]
  | inr v =>
      simp [ForwardQSimpleLetterSmooth.rootLabel,
        CutPreservation.underlyingSymbol, h]

/-- The explicit syntactic starred-refinement condition from a variable
word: support containment and one uniform substitution on the whole word. -/
def SyntacticBelow
    {b n l : Nat} {α : Type*}
    (f : VariableWord b n α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  (∀ t : Node b, t ∈ U.tree → t ∈ f.supportNodes) ∧
    ∃ ρ : f.Vars → Sum α U.word.Vars,
      U.word.word = SpanAudit.substitute f.word ρ

/-- Syntactic refinement always implies Track E's span-based refinement. -/
theorem refines_of_syntacticBelow
    {b n l : Nat} {α : Type*}
    (f : VariableWord b n α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (h : SyntacticBelow f U) : Refines f U := by
  rcases h with ⟨hT, ρ, hword⟩
  refine ⟨hT, ?_⟩
  change SpanAudit.span U.word.word ⊆ SpanAudit.span f.word
  rw [hword]
  exact SpanAudit.span_substitute_subset f.word ρ

/-- The reverse implication is valid for two-letter alphabets; it is not
silently imposed on unary alphabets. -/
theorem syntacticBelow_of_refines
    {b n l : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : VariableWord b n α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (h : Refines f U) : SyntacticBelow f U :=
  ⟨h.1, (VariableWord.span_subset_iff_substitution hα f U.word).1 h.2⟩

theorem syntacticBelow_iff_refines
    {b n l : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : VariableWord b n α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    SyntacticBelow f U ↔ Refines f U :=
  ⟨refines_of_syntacticBelow f U, syntacticBelow_of_refines hα f U⟩

/-- Definition-24 simplicity on a semantic colour and the syntactic
refinement domain. The selector is Track E's actual canonical selector,
not a new parameter whose agreement would have to be assumed. -/
def SemanticSyntacticSimpleWithin
    {b n l : Nat} {α γ : Type*}
    (f : VariableWord b n α)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ) : Prop :=
  ∀ (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))),
    SyntacticBelow f U → SyntacticBelow f V →
    (∀ t : Node b,
      t ∈ SkewTree.interior U.tree ↔
        t ∈ SkewTree.interior V.tree) →
    (∀ a : Boundary b l, a ∈ B2 →
      canonicalPoint U a = canonicalPoint V a) →
    (∀ s : BoundedNode b n,
      (∀ a : Boundary b l, a ∈ B2 →
        ¬ IsPrefix (canonicalPoint U a) s.1) →
      CutPreservation.underlyingSymbol U.word s =
        CutPreservation.underlyingSymbol V.word s) →
    color (observe U) = color (observe V)

def SemanticSyntacticSimple
    {b n l : Nat} {α γ : Type*}
    (f : VariableWord b n α)
    (color : SemanticObservation b n α → γ) : Prop :=
  ∃ B2 : Set (Boundary b l),
    SemanticSyntacticSimpleWithin f B2 color

/-- The stronger source-independent span simplicity implies the
semantic syntactic simplicity with no alphabet hypothesis. -/
theorem simpleWithin_to_semanticSyntactic
    {b n l : Nat} {α γ : Type*}
    (f : VariableWord b n α)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ)
    (h : SimpleWithin f B2 (fun U => color (observe U))) :
    SemanticSyntacticSimpleWithin f B2 color := by
  intro U V hU hV hInt hPoints hWord
  apply h U V
    (refines_of_syntacticBelow f U hU)
    (refines_of_syntacticBelow f V hV)
    hInt hPoints
  intro s hs
  calc
    ForwardQSimpleLetterSmooth.rootLabel U s =
      CutPreservation.underlyingSymbol U.word s :=
        rootLabel_eq_underlyingSymbol U s
    _ = CutPreservation.underlyingSymbol V.word s := hWord s hs
    _ = ForwardQSimpleLetterSmooth.rootLabel V s :=
      (rootLabel_eq_underlyingSymbol V s).symm

/-- On a two-letter alphabet, syntactic simplicity is enough to recover
the span-based hypothesis used by Track E's total smooth Q transfer. -/
theorem semanticSyntactic_to_simpleWithin
    {b n l : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : VariableWord b n α)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ)
    (h : SemanticSyntacticSimpleWithin f B2 color) :
    SimpleWithin f B2 (fun U => color (observe U)) := by
  intro U V hU hV hInt hPoints hWord
  apply h U V
    (syntacticBelow_of_refines hα f U hU)
    (syntacticBelow_of_refines hα f V hV)
    hInt hPoints
  intro s hs
  calc
    CutPreservation.underlyingSymbol U.word s =
      ForwardQSimpleLetterSmooth.rootLabel U s :=
        (rootLabel_eq_underlyingSymbol U s).symm
    _ = ForwardQSimpleLetterSmooth.rootLabel V s := hWord s hs
    _ = CutPreservation.underlyingSymbol V.word s :=
      rootLabel_eq_underlyingSymbol V s

theorem simpleWithin_iff_semanticSyntactic
    {b n l : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : VariableWord b n α)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ) :
    SimpleWithin f B2 (fun U => color (observe U)) ↔
      SemanticSyntacticSimpleWithin f B2 color :=
  ⟨simpleWithin_to_semanticSyntactic f B2 color,
    semanticSyntactic_to_simpleWithin hα f B2 color⟩

/-- The full existential B1/B2 simplicity predicate is also equivalent
between the two corrected source presentations, under the explicit
two-letter hypothesis. This does not assert the Ramsey conclusion. -/
theorem simple_iff_semanticSyntactic
    {b n l : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : VariableWord b n α)
    (color : SemanticObservation b n α → γ) :
    Simple (l := l) f (fun U => color (observe U)) ↔
      SemanticSyntacticSimple (l := l) f color := by
  constructor
  · rintro ⟨B2, hB2⟩
    exact ⟨B2, (simpleWithin_iff_semanticSyntactic hα f B2 color).1 hB2⟩
  · rintro ⟨B2, hB2⟩
    exact ⟨B2, (simpleWithin_iff_semanticSyntactic hα f B2 color).2 hB2⟩

end DualTree.ForwardSemiCompleteSemanticBridge
