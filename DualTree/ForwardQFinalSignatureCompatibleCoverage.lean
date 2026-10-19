import DualTree.ForwardQFinalReverseCoverageCriterion

/-!
# Signature-compatible reverse evaluated-Q coverage

Definition 26 of the paper defines [S,f'] as STARRED variable-word
refinements having one fixed signature S, not the full evaluated span
[f']_Λ of all independent final-root assignments.

The previous formalization proved two separate facts:
(1) for EARLY-ANCHORED assignments, the actual corrected fibrewise Q
    evaluation equals the complete ambient f' evaluation everywhere;
(2) reverse coverage of the ENTIRE independent f' span may fail when
    an extra ambient root survives before the cut.

The correct intermediate notion is a source-compatible evaluated word:
there EXISTS one evaluation τ of the OLD source variables such that,
at every retained original f-root u, the value agrees with the
fixed source substitution rho(u) evaluated under τ.

This file proves that every such word in span(f') has an ACTUAL
corrected starred mixed-product Q witness. Conversely, every
evaluated corrected Q image satisfies this same early compatibility,
even before imposing the starred input condition. Thus within the
final ambient span we obtain an exact signature-compatible covering
criterion, without requiring RetainedRootsAreOld.

The next genuinely source-facing obligation is to prove that the
ACTUAL Definition 26 fixed-signature restriction on starred variable
words implies the source-compatible condition on their evaluated
spans, and to upgrade the result from evaluations of words to the
required starred variable-word Q image. Nothing here falsely equates
[S,f'] with the full span(f').
-/

namespace DualTree.ForwardQFinalSignatureCompatibleCoverage

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalWholeFibreQEvaluation
open ForwardQFinalEarlyFibreAssignment

/-- An evaluated ambient tree word respects the OLD fixed signature
on every original f-variable fibre rooted at/before the cut, for ONE
common assignment to the old source variables. -/
def EarlyCompatibleValue
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (ψ : TreeWord b n α) : Prop :=
  ∃ τ : g.core.source.word.Vars → α,
    ∀ u : g.ambient.Vars,
      ForwardAux u.1.1 g.core.cut →
      ψ u.1 = SpanAudit.evalSymbol τ (g.substitution u)

/-- Every evaluation of the ACTUAL fibrewise corrected Q, even at an
arbitrary enlarged mixed input, has the fixed early source signature
under the same old variable assignment that evaluates the Q word. -/
theorem earlyCompatible_of_fibreQ_eval
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (τ : g.core.source.word.Vars → α) :
    EarlyCompatibleValue g
      (SpanAudit.eval
        (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w) τ) := by
  refine ⟨τ, ?_⟩
  intro u hu
  have hsource :
      g.core.source.word.word u.1 = g.substitution u := by
    rw [g.source_substitution]
    simp [SpanAudit.substitute,g.ambient.atRoot u]
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1 = g.substitution u := by
    exact (ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback w u.1 u (g.ambient.atRoot u) hu).trans hsource
  change SpanAudit.evalSymbol τ
    (ForwardQAmbientFibreSymbol.fibreQSymbol
      g fallback w u.1) =
    SpanAudit.evalSymbol τ (g.substitution u)
  rw [hQ]

/-- Within span(f'), early-value compatibility forces the
independently chosen final-root assignment to ALREADY be its own
source anchoring; no no-extra-retained-root hypothesis is needed. -/
theorem anchored_eq_of_early_compatible
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (ψ : TreeWord b n α)
    (hψ :
      (interpolatedFinalWord
        g f (fun a : α => a) fallback).eval σ = ψ)
    (hearly :
      ∀ u : g.ambient.Vars,
        ForwardAux u.1.1 g.core.cut →
        ψ u.1 = SpanAudit.evalSymbol τ (g.substitution u)) :
    anchoredAssignment g f τ σ = σ := by
  funext r
  by_cases hb : ForwardAux r.1.1 g.core.cut
  · let u : g.ambient.Vars :=
      ⟨r.1,boundedFinalRoots_subset_original g f r⟩
    have hfroot :
        (interpolatedFinalWord
          g f (fun a : α => a) fallback).word r.1 = Sum.inr r :=
      (interpolatedFinalWord
        g f (fun a : α => a) fallback).atRoot r
    have hrootval :
        ((interpolatedFinalWord
          g f (fun a : α => a) fallback).eval σ) r.1 = σ r := by
      change SpanAudit.evalSymbol σ
        ((interpolatedFinalWord
          g f (fun a : α => a) fallback).word r.1) = σ r
      rw [hfroot]
      rfl
    have heval : σ r = ψ r.1 :=
      hrootval.symm.trans (congrFun hψ r.1)
    change (if h : ForwardAux r.1.1 g.core.cut then
      SpanAudit.evalSymbol τ (g.substitution u)
      else σ r) = σ r
    rw [dif_pos hb]
    exact (hearly u hb).symm.trans heval.symm
  · simp [anchoredAssignment,hb]

/-- Every signature-compatible element of the FINAL word's
evaluated span is realized by a GENUINE corrected starred Q input
from the post-Ramsey mixed-word span, evaluated on old source
variables. No hypothesis on retained-root equality is needed. -/
theorem compatible_final_span_has_actual_starred_Q_witness
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (ψ : TreeWord b n α)
    (hspan :
      ψ ∈ (interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hcompat : EarlyCompatibleValue g ψ) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ := by
  obtain ⟨σ,hψ⟩ := hspan
  obtain ⟨τ,hearly⟩ := hcompat
  have hanchor :
      anchoredAssignment g f τ σ = σ :=
    anchored_eq_of_early_compatible
      g f fallback σ τ ψ hψ hearly
  let w := liftedStarred g.core fallback
    (ForwardQFinalInducedStarredPoint.inducedStarredInput
      g f fallback σ hq)
  have heq :=
    ForwardQFinalWholeDomainEvaluation.inducedFibreQ_eval_eq_final_eval
      hb g f fallback τ σ hq
  rw [hanchor] at heq
  exact ⟨w,τ,heq.trans hψ⟩

/-- Exact covering criterion on the FINAL evaluated span.
The backward direction works for all enlarged inputs, so in
particular for the actual corrected starred mixed-product Q. -/
theorem compatible_iff_actual_starred_Q_coverage_on_final_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (ψ : TreeWord b n α)
    (hspan :
      ψ ∈ (interpolatedFinalWord
        g f (fun a : α => a) fallback).span) :
    EarlyCompatibleValue g ψ ↔
      ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback)
        (τ : g.core.source.word.Vars → α),
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w).word.eval τ = ψ := by
  constructor
  · intro h
    exact compatible_final_span_has_actual_starred_Q_witness
      hb g f fallback hq ψ hspan h
  · rintro ⟨w,τ,heq⟩
    have hsource :=
      earlyCompatible_of_fibreQ_eval g fallback w.1 τ
    change SpanAudit.eval
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w.1) τ = ψ at heq
    rw [heq] at hsource
    exact hsource

/-- Reusable intermediate bridge toward Definition 26:
any family of refinements whose evaluations lie in the final span
and satisfy the FIXED early signature compatibility has its
evaluated span covered by actual corrected starred Q outputs.
It remains to derive the two premises from the paper's actual
starred fixed-signature definition, rather than postulate them. -/
theorem source_signature_compatible_refinement_covered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (h : VariableWord b n α)
    (hspan :
      h.span ⊆ (interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hfixed :
      ∀ ψ : TreeWord b n α, ψ ∈ h.span →
        EarlyCompatibleValue g ψ)
    (ψ : TreeWord b n α) (hψ : ψ ∈ h.span) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ :=
  compatible_final_span_has_actual_starred_Q_witness
    hb g f fallback hq ψ (hspan hψ) (hfixed ψ hψ)

end DualTree.ForwardQFinalSignatureCompatibleCoverage
