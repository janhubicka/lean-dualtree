import DualTree.ForwardQVariableSpanCollapse

/-!
# Exact criterion for preserving evaluated cone-variable spans

The preceding obstruction proves that identifying two DISTINCT
actually-occurring local variable names strictly shrinks the
two-letter evaluated span. Here we also prove the converse:

For a PURE variable-name translation rho : κ → ν, the evaluated
span is preserved exactly when rho is injective on the subset of
κ whose variables actually occur in the raw local word.

This is stronger and more accurate than requiring global
injectivity on unused names. The positive direction constructs
an evaluation of the target names by choosing an inverse ONLY
on the image of occurring source names; the unused names receive
a fixed fallback letter.

The final specialization uses the genuine forward-corrected
full-frontier raw local words and the old source-variable subtype.
It gives the exact algebraic remaining obligation for preserving
the FULL local Hales--Jewett span under a root translation.
No existence of the paper's required injective old-root transport,
and no global Ramsey theorem, is asserted.
-/

namespace DualTree.ForwardQSpanExactInjectivity

/-- A local variable name occurs if it actually appears at some
position of the source word, not merely in the declared type. -/
def Occurs {ι κ α : Type*} (w : ι → Sum α κ) (v : κ) : Prop :=
  ∃ i : ι, w i = Sum.inr v

/-- The name translation only needs to be injective on actual
occurrences; unused local names may be collapsed freely. -/
def InjectiveOnOccurrences
    {ι κ ν α : Type*}
    (w : ι → Sum α κ)
    (ρ : κ → ν) : Prop :=
  ∀ (u v : κ), Occurs w u → Occurs w v →
    ρ u = ρ v → u = v

/-- For any nonempty alphabet, a pure local variable translation
injective on occurring names preserves ALL evaluated words.
The extension assignment on target names is arbitrary outside
the image of occurring names. -/
theorem span_eq_of_injective_on_occurrences
    {ι κ ν α : Type*}
    (w : ι → Sum α κ)
    (ρ : κ → ν)
    (fallback : α)
    (hinj : InjectiveOnOccurrences w ρ) :
    SpanAudit.span
        (SpanAudit.substitute w
          (fun k => (Sum.inr (ρ k) : Sum α ν))) =
      SpanAudit.span w := by
  apply Set.Subset.antisymm
  · exact SpanAudit.span_substitute_subset w
      (fun k => (Sum.inr (ρ k) : Sum α ν))
  · intro value hv
    rcases hv with ⟨σ, hσ⟩
    classical
    let τ : ν → α := fun q =>
      if h : ∃ v : κ, Occurs w v ∧ ρ v = q then
        σ (Classical.choose h)
      else fallback
    have hτ :
        ∀ v : κ, Occurs w v → τ (ρ v) = σ v := by
      intro v hv
      have hsome :
          ∃ u : κ, Occurs w u ∧ ρ u = ρ v :=
        ⟨v, hv, rfl⟩
      have hc :
          Occurs w (Classical.choose hsome) ∧
            ρ (Classical.choose hsome) = ρ v :=
        Classical.choose_spec hsome
      have hname : Classical.choose hsome = v :=
        hinj _ _ hc.1 hv hc.2
      simp [τ, hsome, hname]
    refine ⟨τ, ?_⟩
    have heval :
        SpanAudit.eval
          (SpanAudit.substitute w
            (fun k => (Sum.inr (ρ k) : Sum α ν))) τ =
        SpanAudit.eval w σ := by
      funext i
      cases hi : w i with
      | inl a =>
          simp [SpanAudit.eval, SpanAudit.substitute,
            SpanAudit.evalSymbol, hi]
      | inr k =>
          have hk : Occurs w k := ⟨i, hi⟩
          simpa [SpanAudit.eval, SpanAudit.substitute,
            SpanAudit.evalSymbol, hi] using hτ k hk
    exact heval.trans hσ

/-- If the evaluated span is preserved over a two-letter alphabet,
then TWO different occurring names cannot have the same image.
This is the converse of the positive theorem above. -/
theorem injective_on_occurrences_of_span_eq
    {ι κ ν α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (w : ι → Sum α κ)
    (ρ : κ → ν)
    (heq :
      SpanAudit.span
        (SpanAudit.substitute w
          (fun k => (Sum.inr (ρ k) : Sum α ν))) =
      SpanAudit.span w) :
    InjectiveOnOccurrences w ρ := by
  intro u v hu hv hρ
  by_contra hne
  rcases hu with ⟨i, hi⟩
  rcases hv with ⟨j, hj⟩
  have hspan :
      SpanAudit.span w ⊆
        SpanAudit.span
          (SpanAudit.substitute w
            (fun k => (Sum.inr (ρ k) : Sum α ν))) := by
    rw [heq]
  exact (ForwardQVariableSpanCollapse.original_span_not_subset_of_collapsed_span
    hα w (fun k => (Sum.inr (ρ k) : Sum α ν))
    i j u v hne hi hj (congrArg Sum.inr hρ)) hspan

/-- For alphabets with at least two letters, full evaluated
span preservation is equivalent to injectivity on precisely the
occurring local variable names. -/
theorem span_eq_iff_injective_on_occurrences
    {ι κ ν α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (w : ι → Sum α κ)
    (ρ : κ → ν) :
    SpanAudit.span
        (SpanAudit.substitute w
          (fun k => (Sum.inr (ρ k) : Sum α ν))) =
      SpanAudit.span w ↔
      InjectiveOnOccurrences w ρ := by
  constructor
  · exact injective_on_occurrences_of_span_eq hα w ρ
  · intro hinj
    rcases hα with ⟨a, _, _⟩
    exact span_eq_of_injective_on_occurrences w ρ a hinj

open ForwardSourceQTree

/-- Exact span preservation test for the raw word in ANY
actual complete-support frontier cone i. The target variable
names are the source's genuinely typed old interior roots. -/
theorem frontier_raw_span_eq_iff_occurring_root_injective
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : ForwardQFullFrontierWord.Index c →
      BoundedNode b n → Sum (Sum α (Fin (m + 1))) κ)
    (root : ForwardQFullFrontierWord.Index c →
      κ → c.source.word.Vars)
    (i : ForwardQFullFrontierWord.Index c)
    (hβ : SpanAudit.HasTwoLetters (Sum α (Fin (m + 1)))) :
    SpanAudit.span
        (SpanAudit.substitute (raw i)
          (fun z => (Sum.inr (root i z) :
            Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) =
      SpanAudit.span (raw i) ↔
        InjectiveOnOccurrences (raw i) (root i) :=
  span_eq_iff_injective_on_occurrences hβ (raw i) (root i)

end DualTree.ForwardQSpanExactInjectivity
