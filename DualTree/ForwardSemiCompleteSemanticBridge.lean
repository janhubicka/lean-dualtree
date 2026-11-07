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
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardSourceQTree
open ForwardQAllExteriorFibres

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


/-!
## Actual Q images: unary-safe semantic simple-to-smooth transfer

The abstract syntax/span equivalence above needs two different letters
only in its reverse direction. Actual Q outputs do not need this
assumption: their entire word is an EXPLICIT substitution of the ambient
word, and their support is contained in the ambient support.

The following direct proof uses only syntactic simplicity on these
actual outputs, the canonical boundary-to-D2 theorem, equality of
interiors and the cone-exterior rooted-symbol comparison. It works
for every original alphabet with a supplied fallback element.
-/

/-- Every genuine corrected starred Q output is a syntactic refinement
of the ambient word, with no alphabet-size hypothesis. -/
theorem Q_syntacticBelow_ambient
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    SyntacticBelow c.ambient (fibreQStarredWord hb c fallback w) := by
  have href : Refines c.ambient
      (fibreQStarredWord hb c fallback w) :=
    (refines_iff_frame c _).2
      (ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient
        hb c fallback w)
  refine ⟨href.1, ?_⟩
  · refine ⟨ForwardQAmbientFibreSymbol.fibreSubstitution c fallback w.1, ?_⟩
    funext s
    calc
      (fibreQStarredWord hb c fallback w).word.word s =
        ForwardQAmbientFibreSymbol.fibreQSymbol c fallback w.1 s :=
          fibreQStarredWord_symbol hb c fallback w s
      _ = SpanAudit.substitute c.ambient.word
            (ForwardQAmbientFibreSymbol.fibreSubstitution
              c fallback w.1) s :=
          congrFun (ForwardQAmbientFibreSpan.fibreQSymbol_eq_substitute
            c fallback w.1) s

/-- A semantic syntactically-simple colour is smooth on the actual
corrected Q starred space for *every* alphabet, including singleton
alphabets. No two-letter or synthetic selector hypothesis is used. -/
theorem semanticSyntacticSimpleWithin_Q_pullback_smooth
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ)
    (hsimple : SemanticSyntacticSimpleWithin c.ambient B2 color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (gamma1OfBoundaryB2 hb c.core B2) x.1 y.1) :
    color (observe (fibreQStarredWord hb c fallback x)) =
      color (observe (fibreQStarredWord hb c fallback y)) := by
  apply hsimple
    (fibreQStarredWord hb c fallback x)
    (fibreQStarredWord hb c fallback y)
    (Q_syntacticBelow_ambient hb c fallback x)
    (Q_syntacticBelow_ambient hb c fallback y)
  · intro t
    exact ForwardQSimpleLetterSmooth.Q_interiors_eq
      hb c fallback x y t
  · intro a ha
    rw [canonicalPoint_actual_Q hb c fallback x a,
      canonicalPoint_actual_Q hb c fallback y a]
    have hg :
        gamma1OfBoundaryB2 hb c.core B2
            ((boundaryToD2 hb c.core) a) = false :=
      (gamma2_iff_boundaryB2 hb c.core B2 a).2 ha
    exact congrArg Subtype.val
      (ForwardQAmbientFibreSmoothObservable.gamma2_Q_markedProjection_eq_of_smooth
        c fallback x y
        (gamma1OfBoundaryB2 hb c.core B2) hxy
        ((boundaryToD2 hb c.core) a) hg)
  · intro s hout
    have houtside :
        ∀ j : MixedProduct.BulletIndex (kind c.core),
          gamma1OfBoundaryB2 hb c.core B2 j = false →
          ¬ IsPrefix
            (markedProjection c.core
              (ForwardQEnlargedConstantWords.eraseAux
                c.core fallback x.1) j).1 s.1 := by
      intro j hj
      have ha :
          ((boundaryToD2 hb c.core).symm j) ∈ B2 := by
        apply (gamma2_iff_boundaryB2 hb c.core B2
          ((boundaryToD2 hb c.core).symm j)).1
        simpa only [Equiv.apply_symm_apply] using hj
      have hnode := hout ((boundaryToD2 hb c.core).symm j) ha
      rw [canonicalPoint_actual_Q hb c fallback x
        ((boundaryToD2 hb c.core).symm j),
        Equiv.apply_symm_apply] at hnode
      exact hnode
    have hword :=
      starred_Q_word_eq_outside_gamma2_cones
        hb c fallback x y
        (gamma1OfBoundaryB2 hb c.core B2)
        hxy s houtside
    change ForwardQAmbientFibreSymbol.fibreQSymbol
        c fallback x.1 s =
      ForwardQAmbientFibreSymbol.fibreQSymbol
        c fallback y.1 s at hword
    calc
      CutPreservation.underlyingSymbol
          (fibreQStarredWord hb c fallback x).word s =
        ForwardQSimpleLetterSmooth.rootLabel
          (fibreQStarredWord hb c fallback x) s :=
            (rootLabel_eq_underlyingSymbol
              (fibreQStarredWord hb c fallback x) s).symm
      _ = ForwardQSimpleLetterSmooth.rootLabel
          (fibreQStarredWord hb c fallback y) s := by
            rw [ForwardQSimpleLetterSmooth.rootLabel_fibreQ
                  hb c fallback x s,
                ForwardQSimpleLetterSmooth.rootLabel_fibreQ
                  hb c fallback y s]
            exact congrArg
              (fun q : Sum α c.core.source.word.Vars =>
                match q with
                | Sum.inl a => Sum.inl a
                | Sum.inr v => Sum.inr v.1) hword
      _ = CutPreservation.underlyingSymbol
          (fibreQStarredWord hb c fallback y).word s :=
            rootLabel_eq_underlyingSymbol
              (fibreQStarredWord hb c fallback y) s

/-- Any syntactically simple semantic colour has a total smooth
extension of its genuine Q pullback, without two-letter assumptions.
Outside the starred domain the extension uses the supplied fallback
colour only to choose a representative of unrealized smooth classes. -/
theorem exists_total_semanticSyntacticSimpleWithin_Q_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (B2 : Set (Boundary b l))
    (color : SemanticObservation b n α → γ)
    (hsimple : SemanticSyntacticSimpleWithin c.ambient B2 color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (observe (fibreQStarredWord hb c fallback w))) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (gamma1OfBoundaryB2 hb c.core B2) x y → total x = total y) := by
  let D : Set (ForwardQEnlargedConstantWords.EnlargedInput c.core) :=
    {w | ForwardQActualStarredSpace.IsStarred c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w)}
  let pulled :
      {w : ForwardQEnlargedConstantWords.EnlargedInput c.core //
        w ∈ D} → γ :=
    fun w => color (observe
      (fibreQStarredWord hb c fallback ⟨w.1, w.2⟩))
  have hcompatible :
      ∀ (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
        (hx : x ∈ D) (hy : y ∈ D),
        MixedProduct.SmoothRelated
          (gamma1OfBoundaryB2 hb c.core B2) x y →
          pulled ⟨x, hx⟩ = pulled ⟨y, hy⟩ := by
    intro x y hx hy hxy
    exact semanticSyntacticSimpleWithin_Q_pullback_smooth
      hb c fallback B2 color hsimple ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨total, hagree, hsmooth⟩ :=
    MixedProduct.exists_smooth_extension
      (gamma1OfBoundaryB2 hb c.core B2)
      D pulled fallbackColor hcompatible
  refine ⟨total, ?_, hsmooth⟩
  intro x
  exact hagree x.1 x.2

/-- Quantifying the Definition-24 partition gives the existential
total smooth pullback required for a mixed-product Ramsey input.
This result does not assert existence of a Ramsey word. -/
theorem semanticSyntacticSimple_exists_total_smooth_Q_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (color : SemanticObservation b n α → γ)
    (hsimple : SemanticSyntacticSimple c.ambient color) :
    ∃ gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool,
      ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
        (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback,
          total w.1 = color (observe (fibreQStarredWord hb c fallback w))) ∧
        (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
          MixedProduct.SmoothRelated gamma1 x y → total x = total y) := by
  obtain ⟨B2, hB2⟩ := hsimple
  exact ⟨gamma1OfBoundaryB2 hb c.core B2,
    exists_total_semanticSyntacticSimpleWithin_Q_pullback
      hb c fallback fallbackColor B2 color hB2⟩

end DualTree.ForwardSemiCompleteSemanticBridge
