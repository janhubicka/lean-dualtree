import DualTree.ForwardQFinalExactOutputWord
import DualTree.MixedProduct

/-!
# Change the constant alphabet of an actual mixed variable word

The enlarged alphabet of corrected Lemma 27 is alpha + Fin(m+1),
while the local mixed-product Ramsey variable word may first be
presented with alphabet alpha. There must be a genuine typed
variable word over the enlarged alphabet, retaining precisely its
variable supports and D1/D2 marked-point constraints.

This module constructs this lift for ordinary, k-variable, and
mixed-product variable words, then proves that any choice of one
enlarged letter for EACH actual local variable yields a true
member of the lifted mixed-product span, provided the retained
marked-point coordinates were legal.

No claim is made that independent pointwise encodings of a requested
Q-output automatically give this uniform choice. That requires
the separate same-fibre transport from the interpolated f' span.
-/

namespace DualTree.ForwardQFinalMixedAlphabetSpan

/-- Change ONLY alphabet constants of an ordinary variable word.
Every actual dependent root, below-root law and support is retained. -/
def mapVariableWordConstants
    {b n : Nat} {α β : Type*}
    (f : DualTree.VariableWord b n α)
    (φ : α → β) : DualTree.VariableWord b n β where
  support := f.support
  support_nodup := f.support_nodup
  word := fun s => Sum.map φ id (f.word s)
  atRoot := by
    intro v
    change Sum.map φ id (f.word v.1) = Sum.inr v
    rw [f.atRoot v]
    rfl
  below := by
    intro v s h
    change Sum.map φ id (f.word s) = Sum.inr v at h
    cases hs : f.word s with
    | inl a =>
        simp [hs] at h
    | inr w =>
        have hw : w = v := by
          simpa [hs] using h
        subst w
        exact f.below v s hs

/-- A uniform assignment to the ORIGINAL dependent variables gives
a genuine evaluated word of the alphabet-lifted variable word. -/
theorem mapVariableWordConstants_evaluation_mem_span
    {b n : Nat} {α β : Type*}
    (f : DualTree.VariableWord b n α)
    (φ : α → β)
    (σ : f.Vars → β) :
    (fun s : BoundedNode b n =>
      match f.word s with
      | Sum.inl a => φ a
      | Sum.inr v => σ v) ∈
    (mapVariableWordConstants f φ).span := by
  refine ⟨σ, ?_⟩
  funext s
  cases hs : f.word s with
  | inl a =>
      simp [VariableWord.eval, SpanAudit.eval,
        SpanAudit.evalSymbol, mapVariableWordConstants, hs]
  | inr v =>
      simp [VariableWord.eval, SpanAudit.eval,
        SpanAudit.evalSymbol, mapVariableWordConstants, hs]

/-- A complete k-variable word remains a complete k-variable word
when alphabet constants are injected into another alphabet. -/
def mapKWordConstants
    {b n k : Nat} {α β : Type*}
    {aux : Node b → Node b → Bool}
    (f : KVariableWord b n k α aux)
    (φ : α → β) : KVariableWord b n k β aux where
  toVariableWord := mapVariableWordConstants f.toVariableWord φ
  complete_support := by
    exact f.complete_support

/-- Lift the ACTUAL mixed-product variable word, keeping all variable
supports and both D1 and D2 marked-point geometry literally intact. -/
def mapMixedWordConstants
    {b n d k : Nat} {α β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (φ : α → β) :
    MixedProduct.VariableWord b n d k β aux kind where
  vector := {
    components := fun i => mapKWordConstants (f.vector.components i) φ
    vector_complete := by
      exact f.vector.vector_complete }
  upLeaves := f.upLeaves
  upLeaves_nodup := f.upLeaves_nodup
  upLeaves_card := f.upLeaves_card
  up_support_skew := by
    intro i
    exact f.up_support_skew i

/-- An actual mixed-product point whose ordinary coordinate words
come from ONE choice of target letter per old local variable.
D1 and D2 markers are taken unchanged from a given base point. -/
def inputOfComponentChoices
    {b n d k : Nat} {α β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (φ : α → β)
    (base : MixedProduct.Element b n d α kind)
    (choices : ∀ i : Fin d, (f.vector.components i).Vars → β) :
    MixedProduct.Element b n d β kind where
  words := fun i s =>
    match (f.vector.components i).word s with
    | Sum.inl a => φ a
    | Sum.inr v => choices i v
  upPoint := base.upPoint
  bulletPoint := base.bulletPoint

/-- Uniform assignments at actual component variables, together
with legal ORIGINAL marked points, give a genuine point in the
span of the lifted mixed-product variable word. -/
theorem inputOfComponentChoices_mem_span
    {b n d k : Nat} {α β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (φ : α → β)
    (base : MixedProduct.Element b n d α kind)
    (hbase : base ∈ f.span)
    (choices : ∀ i : Fin d, (f.vector.components i).Vars → β) :
    inputOfComponentChoices f φ base choices ∈
      (mapMixedWordConstants f φ).span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change
      (fun s : BoundedNode b n =>
        match (f.vector.components i).word s with
        | Sum.inl a => φ a
        | Sum.inr v => choices i v) ∈
        SpanAudit.span (fun s : BoundedNode b n =>
          Sum.map φ id ((f.vector.components i).word s))
    refine ⟨choices i, ?_⟩
    funext s
    cases hs : (f.vector.components i).word s with
    | inl a =>
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hs]
    | inr v =>
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hs]
  · exact hbase.2.1
  · exact hbase.2.2

/-- The lifted mixed input is CONSTANT ON EACH ACTUAL COMPONENT
VARIABLE FIBRE, not merely on a chosen enumeration of its roots. -/
theorem inputOfComponentChoices_constant_on_fibre
    {b n d k : Nat} {α β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (φ : α → β)
    (base : MixedProduct.Element b n d α kind)
    (choices : ∀ i : Fin d, (f.vector.components i).Vars → β)
    (i : Fin d)
    (v : (f.vector.components i).Vars)
    (s : BoundedNode b n)
    (hs : (f.vector.components i).word s = Sum.inr v) :
    (inputOfComponentChoices f φ base choices).words i s =
      (inputOfComponentChoices f φ base choices).words i v.1 := by
  have hroot := (f.vector.components i).toVariableWord.atRoot v
  simp [inputOfComponentChoices, hs, hroot]

end DualTree.ForwardQFinalMixedAlphabetSpan
