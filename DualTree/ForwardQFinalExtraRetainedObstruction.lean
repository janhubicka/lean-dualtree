import DualTree.ForwardQFinalEarlySpanObstruction

/-!
# Reverse Q-span coverage fails whenever the final word retains an extra early root

The corrected Lemma 27 construction proves that actual Q evaluations occur
in the final f' span after anchoring the early variable values.  The
opposite, unrestricted spanning assertion is generally false.

The earlier checked obstruction covered two distinct early ambient roots
which the source refinement rho maps to the SAME old source symbol.

This module removes that artificial extra hypothesis: if a retained early
root u is NOT one of the original source starred-word variable roots, rho(u)
has only two possibilities.

* rho(u) is a constant.  Then every Q evaluation has that constant at u,
  while the constructed f' retains u as an independent variable.
* rho(u) is an old source variable v.  By the verified atRoot axiom,
  rho already fixes v at its original ambient root.  Thus rho identifies
  the new retained root u with that distinct old root, and the previous
  two-root obstruction applies.

Over any alphabet with two letters, either case produces an evaluation of
the ACTUAL final f' word outside the union of evaluations of ALL fibrewise
corrected Q images (even without imposing the starred input condition).

The theorem does NOT assert that an extra retained root exists in every
legal frame.  Its existence is the precise remaining geometric/counting
hypothesis for applying this obstruction to a given Lemma 27 instance.
It does NOT refute the final Ramsey statement, and it only concerns the
corrected forward-auxiliary version, not the printed reverse-order Q.
-/

namespace DualTree.ForwardQFinalExtraRetainedObstruction

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalEarlyFibreAssignment

/-- At every retained original ambient root the refined word really emits
its OWN final variable, not a constant or old source variable. -/
theorem finalWord_at_early_original_root
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (u : g.ambient.Vars)
    (hu : ForwardAux u.1.1 g.core.cut) :
    (interpolatedFinalWord g f (fun a : α => a) fallback).word u.1 =
      Sum.inr (earlyFinalRoot g f u hu) := by
  change SpanAudit.substitute g.ambient.word
    (globalRootSymbol g f (fun a : α => a) fallback) u.1 =
      Sum.inr (earlyFinalRoot g f u hu)
  rw [SpanAudit.substitute, g.ambient.atRoot u]
  exact globalRootSymbol_early g f (fun a : α => a) fallback u hu

/-- If rho freezes even ONE retained original f-variable to a constant,
the unrestricted reverse Q-span covering is impossible over a two-letter
alphabet.  The fibrewise Q decoder uses rho on early f fibres for EVERY
enlarged mixed input, whereas f' has a genuinely free variable at u. -/
theorem not_every_final_evaluation_of_early_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (u : g.ambient.Vars)
    (hu : ForwardAux u.1.1 g.core.cut)
    (a : α)
    (hρ : g.substitution u = Sum.inl a) :
    ∃ ψ : TreeWord b n α,
      ψ ∈ (interpolatedFinalWord g f
        (fun x : α => x) fallback).span ∧
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
        (τ : g.core.source.word.Vars → α),
        SpanAudit.eval
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w) τ ≠ ψ := by
  classical
  obtain ⟨a₀, a₁, hne⟩ := hα
  have hother : ∃ d : α, d ≠ a := by
    by_cases ha : a = a₀
    · refine ⟨a₁, ?_⟩
      intro heq
      exact hne (ha.symm.trans heq.symm)
    · exact ⟨a₀, fun heq => ha heq.symm⟩
  obtain ⟨d, hd⟩ := hother
  let r := earlyFinalRoot g f u hu
  let σ : FinalRoot g f → α := fun v => if v = r then d else a
  let ψ : TreeWord b n α :=
    (interpolatedFinalWord g f
      (fun x : α => x) fallback).eval σ
  have hψu : ψ u.1 = d := by
    change SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f
        (fun x : α => x) fallback).word u.1) = d
    rw [finalWord_at_early_original_root g f fallback u hu]
    simp [SpanAudit.evalSymbol, σ, r]
  refine ⟨ψ, ⟨σ, rfl⟩, ?_⟩
  intro w τ heq
  have hsource :
      g.core.source.word.word u.1 = Sum.inl a := by
    rw [g.source_substitution]
    simp [SpanAudit.substitute, g.ambient.atRoot u, hρ]
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1 = Sum.inl a := by
    rw [ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback w u.1 u (g.ambient.atRoot u) hu]
    exact hsource
  have hQu :
      SpanAudit.eval
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w) τ u.1 = a := by
    change SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1) = a
    rw [hQ]
    rfl
  have hcontr : d = a := by
    calc
      d = ψ u.1 := hψu.symm
      _ = SpanAudit.eval
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w) τ u.1 := (congrFun heq u.1).symm
      _ = a := hQu
  exact hd hcontr

/-- Any retained early ambient variable root NOT among the old source
variable roots obstructs unrestricted reverse Q-span coverage.
The source substitution must either freeze it (constant case) or
identify it with an already fixed old source root (variable case). -/
theorem not_every_final_evaluation_of_extra_retained_root
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (u : g.ambient.Vars)
    (hu : ForwardAux u.1.1 g.core.cut)
    (hnotold : u.1 ∉ g.core.source.word.support) :
    ∃ ψ : TreeWord b n α,
      ψ ∈ (interpolatedFinalWord g f
        (fun x : α => x) fallback).span ∧
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
        (τ : g.core.source.word.Vars → α),
        SpanAudit.eval
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w) τ ≠ ψ := by
  cases hρ : g.substitution u with
  | inl a =>
      exact not_every_final_evaluation_of_early_constant
        g f fallback hα u hu a hρ
  | inr v =>
      let w := ForwardQAmbientFibreFrame.ambientAtSourceRoot g v
      have hw : ForwardAux w.1.1 g.core.cut :=
        ForwardQAmbientFibreFrame.source_root_before_cut g v
      have hne : u.1 ≠ w.1 := by
        intro heq
        apply hnotold
        have hv : u.1 = v.1 := by
          simpa only [w,
            ForwardQAmbientFibreFrame.ambientAtSourceRoot_node] using heq
        rw [hv]
        exact v.2
      have hcollapse : g.substitution u = g.substitution w := by
        calc
          g.substitution u = Sum.inr v := hρ
          _ = g.substitution w :=
            (ForwardQAmbientFibreFrame.source_substitution_fixes_old_root
              g v).symm
      exact
        ForwardQFinalEarlySpanObstruction.not_every_final_evaluation_is_Q_evaluation
          g f fallback hα u w hu hw hne hcollapse

end DualTree.ForwardQFinalExtraRetainedObstruction
