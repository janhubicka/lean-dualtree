import DualTree.ForwardQFinalEnlargedAnchoredEvaluation
import DualTree.ForwardQFinalUnsafeFibreFallback

/-!
# Whole-domain corrected Q/f' evaluation for GENUINE enlarged Ramsey words

The actual post-Corollary-22 local Ramsey word has alphabet
α ⊕ Fin (m+1). The enlarged final ambient word must decode fixed
auxiliary letters to genuine retained old roots rather than replace
them by original constants. This has now been done, including actual
starred mixed input construction and whole projected-fibre comparison.

This file closes the other original ambient-fibre cases under the
canonical old-root anchoring. There are exactly four exhaustive
cases for a bounded original ambient position:
* an original ambient f constant;
* an early f-variable root at/before the forward cut;
* a late safe P_i(z) variable root, handled by the verified
  genuine enlarged projected-fibre theorem;
* a late unsafe/no-projection original f root, at which BOTH
  constructions emit the same explicit original fallback letter.

We thereby get literal equality of evaluated tree words on ALL
ambient positions, and a concrete actual enlarged STARRED mixed
input in the full local Ramsey span whose evaluated corrected-Q
output belongs to the enlarged final f' span.

As before, the final assignment is necessarily ANCHORED on old
source roots. This does not claim unrestricted reverse coverage of
every independent final-root evaluation, printed reverse-lex W_*,
or the numerical Corollary-22 Ramsey induction.
-/

namespace DualTree.ForwardQFinalEnlargedWholeDomainEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedLocalSymbols
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQFinalEnlargedProjectedEval
open ForwardQFinalEnlargedAnchoredEvaluation
open ForwardQFinalSafeAddressLookup

/-- Every genuine original f root at/before the corrected
forward cut survives among the independent final roots.
The enlarged global substitution fixes it exactly; auxiliary
constant decoding in OTHER late fibres does not alter this. -/
theorem enlargedGlobalRootSymbol_early
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    enlargedGlobalRootSymbol g f fallback u =
      Sum.inr (ForwardQFinalEarlyFibreAssignment.earlyFinalRoot
        g f u hbefore) := by
  have horig :
      (⟨(ForwardQFinalEarlyFibreAssignment.earlyFinalRoot
          g f u hbefore).1,
        boundedFinalRoots_subset_original g f
          (ForwardQFinalEarlyFibreAssignment.earlyFinalRoot
            g f u hbefore)⟩ : g.ambient.Vars) = u :=
    Subtype.ext
      (ForwardQFinalEarlyFibreAssignment.earlyFinalRoot_val
        g f u hbefore)
  have hfix :=
    enlargedGlobalRootSymbol_fixes_final_root g f fallback
      (ForwardQFinalEarlyFibreAssignment.earlyFinalRoot
        g f u hbefore)
  rw [horig] at hfix
  exact hfix

/-- At any original early f-variable fibre, the actual
enlarged Q symbol evaluates to the source refinement rho,
and the enlarged f' retained root evaluates to that same
value under the canonical anchored assignment. -/
theorem enlarged_Q_eval_early_fibre_anchored
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback
          (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
            g f τ σ₀)) s) =
    SpanAudit.evalSymbol
      (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
        g f τ σ₀)
      ((enlargedInterpolatedFinalWord g f fallback).word s) := by
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback
          (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
            g f τ σ₀)) s =
      g.core.source.word.word s :=
    ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback _ s u hs hbefore
  have hSource :
      g.core.source.word.word s = g.substitution u := by
    rw [g.source_substitution]
    simp [SpanAudit.substitute,hs]
  have hFinal :
      (enlargedInterpolatedFinalWord g f fallback).word s =
        enlargedGlobalRootSymbol g f fallback u := by
    change SpanAudit.substitute g.ambient.word
      (enlargedGlobalRootSymbol g f fallback) s =
        enlargedGlobalRootSymbol g f fallback u
    simp [SpanAudit.substitute,hs]
  have hOldEarly :=
    ForwardQFinalEarlyFibreAssignment.anchoredAssignment_early
      g f (fun _ : Sum α (Fin (m+1)) => fallback)
      fallback τ σ₀ u hbefore
  have hEqSymbols :
      enlargedGlobalRootSymbol g f fallback u =
      globalRootSymbol g f
        (fun _ : Sum α (Fin (m+1)) => fallback) fallback u := by
    rw [enlargedGlobalRootSymbol_early g f fallback u hbefore,
      ForwardQFinalEarlyFibreAssignment.globalRootSymbol_early
        g f (fun _ : Sum α (Fin (m+1)) => fallback)
        fallback u hbefore]
  rw [hQ,hSource,hFinal,hEqSymbols]
  exact hOldEarly.symm

/-- Every late original ambient f root with no safe local
projection is absent from the selected final root list, so
the genuine ENLARGED global substitution emits the same
specified original fallback constant. -/
theorem enlargedGlobalRootSymbol_late_no_safe
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    enlargedGlobalRootSymbol g f fallback u = Sum.inl fallback := by
  have hnot : u.1 ∉ boundedFinalRoots g f :=
    ForwardQFinalUnsafeFibreFallback.not_final_root_of_late_no_safe
      g f u hafter hnone
  simp [enlargedGlobalRootSymbol,hnone,hnot]

/-- The actual original fibrewise Q, for an arbitrary enlarged
mixed-product input, sends every late unsafe original ambient
f-fibre to the fallback constant. This does not depend on
any selected D₂ marker or local ordinary word evaluation. -/
theorem enlarged_Q_symbol_late_no_safe
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    ForwardQAmbientFibreSymbol.fibreQSymbol
      g fallback w s = Sum.inl fallback := by
  have hlate :
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w s =
        ForwardQAmbientFibreSymbol.decodeAmbientRoot
          g fallback w u :=
    ForwardQAmbientFibreSymbol.fibreQ_after_cut
      g fallback w s u hs hafter
  rw [hlate]
  cases hsel : ForwardQFullFrontierWord.selectedFrontier
      g.core u.1 with
  | none =>
      simp [ForwardQAmbientFibreSymbol.decodeAmbientRoot,hsel]
  | some i =>
      have hT : u.1.1 ∈ g.core.T :=
        (g.ambient_support_T u.1).1 u.2
      have hunsafe : ¬ InHomTree (k-(m+1))
          (ForwardQActualCoordinateWord.tailOfTNode
            g.core i ⟨u.1.1,hT⟩) := by
        intro hsafe
        obtain ⟨z,hsome⟩ :=
          ForwardQFinalUnsafeFibreFallback.safeAddress_some_of_safe_frontier
            g u i hsel hsafe
        rw [hnone] at hsome
        cases hsome
      exact
        ForwardQFibreDefaults.decodeAmbientRoot_unsafe_fallback
          g fallback w u i hsel hunsafe

/-- At every occurrence of a late unsafe original ambient
f-fibre, the actual enlarged Q and the genuine enlarged final
word have identical evaluations, both equal to fallback. -/
theorem enlarged_Q_eval_late_no_safe
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (enlargedInducedInput g f fallback σ) s) =
    SpanAudit.evalSymbol σ
      ((enlargedInterpolatedFinalWord g f fallback).word s) := by
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ) s =
      Sum.inl fallback :=
    enlarged_Q_symbol_late_no_safe g fallback
      (enlargedInducedInput g f fallback σ)
      u s hs hafter hnone
  have hsub : enlargedGlobalRootSymbol g f fallback u =
      Sum.inl fallback :=
    enlargedGlobalRootSymbol_late_no_safe
      g f fallback u hafter hnone
  have hF :
      (enlargedInterpolatedFinalWord g f fallback).word s =
        Sum.inl fallback := by
    change SpanAudit.substitute g.ambient.word
      (enlargedGlobalRootSymbol g f fallback) s =
        Sum.inl fallback
    simp [SpanAudit.substitute,hs,hsub]
  simp [hQ,hF,SpanAudit.evalSymbol]

/-- Original ambient f-constants are invariant under both the
real corrected Q decoder and the genuine enlarged syntactic
final refinement. They agree under any evaluations of old
source and independently selected final roots. -/
theorem enlarged_Q_eval_on_ambient_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (s : BoundedNode b n)
    (a : α)
    (hs : g.ambient.word s = Sum.inl a) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (enlargedInducedInput g f fallback σ) s) =
    SpanAudit.evalSymbol σ
      ((enlargedInterpolatedFinalWord g f fallback).word s) := by
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ) s =
      Sum.inl a :=
    ForwardQAmbientFibreSymbol.fibreQ_original_constant
      g fallback _ s a hs
  have hF :
      (enlargedInterpolatedFinalWord g f fallback).word s =
        Sum.inl a := by
    change SpanAudit.substitute g.ambient.word
      (enlargedGlobalRootSymbol g f fallback) s = Sum.inl a
    simp [SpanAudit.substitute,hs]
  simp [hQ,hF,SpanAudit.evalSymbol]

/-- Actual whole-domain equality of EVALUATED corrected Q and
the genuine enlarged final word for the canonical anchored
final assignment. The four cases exhaust the original ambient
f-fibres. There is NO additional old-root compatibility,
D₂-order, auxiliary decoding, or Hall requirement. -/
theorem enlarged_Q_eval_eq_final_at
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α)
    (s : BoundedNode b n) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback
          (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
            g f τ σ₀)) s) =
    SpanAudit.evalSymbol
      (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
        g f τ σ₀)
      ((enlargedInterpolatedFinalWord g f fallback).word s) := by
  cases hs : g.ambient.word s with
  | inl a =>
      exact enlarged_Q_eval_on_ambient_constant
        g f fallback
        (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
          g f τ σ₀) τ s a hs
  | inr u =>
      by_cases hbefore : ForwardAux u.1.1 g.core.cut
      · exact enlarged_Q_eval_early_fibre_anchored
          g f fallback τ σ₀ u s hs hbefore
      · cases hsafe : safeAddress g.core u.1.1 with
        | none =>
            exact enlarged_Q_eval_late_no_safe
              g f fallback
              (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
                g f τ σ₀) τ u s hs hbefore hsafe
        | some addr =>
            have hproj :
                (projected g.core addr).1 = u.1.1 :=
              safeAddress_spec g.core u.1.1 addr hsafe
            have hu :
                ForwardQAmbientFibreFrame.ambientAtTRoot
                  g (projected g.core addr).1
                    (projected g.core addr).2 = u := by
              apply Subtype.ext
              apply Subtype.ext
              exact hproj
            have hsfibre :
                g.ambient.word s =
                  Sum.inr
                    (ForwardQAmbientFibreFrame.ambientAtTRoot
                      g (projected g.core addr).1
                        (projected g.core addr).2) := by
              simpa only [hu] using hs
            rcases addr with ⟨i,z⟩
            exact enlarged_Q_projected_fibre_eval_anchored
              g f fallback τ σ₀ i z s hsfibre

/-- The pointwise whole-domain theorem as literal equality of
evaluated tree word FUNCTIONS: Q of a genuine enlarged mixed
input is an actual evaluation of the complete-skew final f'. -/
theorem enlarged_Q_eval_eq_final_eval
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α) :
    SpanAudit.eval
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback
        (enlargedInducedInput g f fallback
          (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
            g f τ σ₀))) τ =
    (enlargedInterpolatedFinalWord g f fallback).eval
      (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
        g f τ σ₀) := by
  funext s
  exact enlarged_Q_eval_eq_final_at g f fallback τ σ₀ s

/-- A concrete evaluation of the ACTUAL legal corrected Q
starred output lies in the span of the honest full enlarged
final word, with arbitrary independent new selected-root values
and the necessary anchoring only at retained old roots. -/
theorem enlarged_starred_Q_eval_mem_final_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α)
    (hq : 0 < q) :
    (ForwardQAmbientFibreLegalWord.fibreQStarredWord
      hb g fallback
      (enlargedInducedStarredInput g f fallback
        (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
          g f τ σ₀) hq)).word.eval τ ∈
      (enlargedInterpolatedFinalWord g f fallback).span := by
  let σ := ForwardQFinalEarlyFibreAssignment.anchoredAssignment
    g f τ σ₀
  refine ⟨σ, ?_⟩
  have hword := enlarged_Q_eval_eq_final_eval
    g f fallback τ σ₀
  change SpanAudit.eval
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ)) τ =
      (enlargedInterpolatedFinalWord g f fallback).eval σ
  exact hword

end DualTree.ForwardQFinalEnlargedWholeDomainEvaluation
