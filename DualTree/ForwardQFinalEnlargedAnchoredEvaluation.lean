import DualTree.ForwardQFinalEnlargedProjectedEval
import DualTree.ForwardQFinalEarlyFibreAssignment

/-!
# Discharge old-root compatibility by the actual final anchoring map

The genuine enlarged-alphabet Q/f' evaluation comparison uses an old
source assignment τ and a final-root assignment σ that agree at every
retained old variable root. This is NOT an additional mathematical
constraint on the independent NEW local roots: the existing
anchoredAssignment g f τ σ₀ forces exactly these old values while
leaving genuinely projected new-root values unchanged.

We prove the agreement for the genuine enlarged local word, rather
than assuming it. Therefore the projected entire-fibre Q/f'
comparison can be invoked for ANY original old-source assignment
and ANY base final-root assignment.

This is still the corrected forward-order construction, not the
paper's printed reverse-lex W_* or complete Q image theorem.
-/

namespace DualTree.ForwardQFinalEnlargedAnchoredEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQFinalEnlargedProjectedEval

/-- Anchoring an arbitrary base final assignment to the old
source-variable assignment τ gives exactly τ's value at every
corresponding retained original source variable root.
This identity does not use a no-extra-retained-roots assumption. -/
theorem anchoredAssignment_old_source_root
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α)
    (v : g.core.source.word.Vars) :
    ForwardQFinalEarlyFibreAssignment.anchoredAssignment
      g f τ σ₀
      (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
        g f v) = τ v := by
  let r := ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot g f v
  have hbefore : ForwardAux r.1.1 g.core.cut := by
    change ForwardAux
      (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
        g f v).1.1 g.core.cut
    rw [ForwardQFinalEnlargedLocalSymbols.oldSourceFinalRoot_underlying
      g f v]
    exact ForwardQAmbientFibreFrame.source_root_before_cut g v
  have horig :
      (⟨r.1,boundedFinalRoots_subset_original g f r⟩ :
        g.ambient.Vars) =
      ForwardQAmbientFibreFrame.ambientAtSourceRoot g v := by
    apply Subtype.ext
    rfl
  change
    (if h : ForwardAux r.1.1 g.core.cut then
      SpanAudit.evalSymbol τ
        (g.substitution
          ⟨r.1,boundedFinalRoots_subset_original g f r⟩)
     else σ₀ r) = τ v
  simp [hbefore, horig,
    ForwardQAmbientFibreFrame.source_substitution_fixes_old_root,
    SpanAudit.evalSymbol]

/-- No compatibility hypothesis needs to be imposed externally:
the genuine anchored assignment supplies it for all old roots,
including those reached by fixed auxiliary local constants. -/
theorem anchored_assignment_is_old_root_compatible
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α) :
    OldRootAssignmentCompatible g f
      (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
        g f τ σ₀) τ := by
  intro v
  exact anchoredAssignment_old_source_root g f τ σ₀ v

/-- The actual corrected fibrewise Q on the genuine enlarged
starred mixed input produced by an ANCHORED final assignment
matches the resulting enlarged final ambient word's evaluation
on EVERY ambient occurrence in a safe P_i(z) fibre. The old
assignment τ and base final assignment σ₀ are arbitrary; no
extra old-root compatibility or D₂-admissibility hypotheses
need to be supplied by the caller. -/
theorem enlarged_Q_projected_fibre_eval_anchored
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ₀ : FinalRoot g f → α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (s : BoundedNode b n)
    (hs : g.ambient.word s =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2)) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback
          (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
            g f τ σ₀)) s) =
    SpanAudit.evalSymbol
      (ForwardQFinalEarlyFibreAssignment.anchoredAssignment
        g f τ σ₀)
      ((ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).word s) := by
  exact enlarged_Q_projected_fibre_eval_eq_final
    g f fallback
    (ForwardQFinalEarlyFibreAssignment.anchoredAssignment g f τ σ₀)
    τ (anchored_assignment_is_old_root_compatible g f τ σ₀)
    i z s hs

end DualTree.ForwardQFinalEnlargedAnchoredEvaluation
