import DualTree.ForwardQFinalRetainedCardinality
import DualTree.ForwardQFinalWholeDomainEvaluation

/-!
# Exact criterion for reverse evaluated-Q coverage by the current final f'

The corrected forward-order Lemma 27 construction always gives a final
complete-skew variable word f' with span(f') included in span(f).
The verified source-facing Q(x_sigma) equality, however, only covers
those f'-assignments whose retained early variables are anchored to
the fixed source refinement rho.

This module identifies the precise missing hypothesis.

RetainedRootsAreOld says EVERY retained original complete-T root (at or
before the corrected forward cut) already belongs to the OLD starred
source-word variable support.  Under that condition, no extra early
values need to be anchored: the old source assignment tau can be read
directly from ANY proposed assignment sigma to f' roots.  The already
verified whole-domain Q equality then covers EVERY evaluation of f'.

Conversely, over a two-letter alphabet, full reverse coverage
requires RetainedRootsAreOld.  An extra retained root is free in f',
but rho must either freeze it to a constant or identify it with an
already fixed old source variable.  The checked extra-root obstruction
then produces an f' evaluation outside ALL Q images.

Thus, under positive b,q and a two-letter alphabet, unrestricted
REVERSE evaluated-Q coverage is equivalent to the precise retained-root
support equality condition.  In particular, it is not a consequence of
complete skewness or of the forward anchored-evaluation equality.

This characterizes the CURRENT repaired forward-Q/f' construction.
It does not identify the printed reverse-auxiliary W_* class, nor
complete the Ramsey-colouring or Lemma 27 induction.
-/

namespace DualTree.ForwardQFinalReverseCoverageCriterion

open ForwardSourceQTree
open ForwardQFinalSupportCut
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalEarlyFibreAssignment
open ForwardQFinalWholeFibreQEvaluation

/-- The exact additional early-root condition needed for unrestricted
reverse coverage: no retained ambient-T root is absent from g'. -/
def RetainedRootsAreOld
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α) : Prop :=
  ∀ t : Node b, t ∈ retained g.core →
    t ∈ g.core.source.word.supportNodes

/-- Regard an original old starred source variable as its own
retained bounded final-root variable. No name allocation is needed. -/
noncomputable def oldSourceFinalRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (v : g.core.source.word.Vars) :
    FinalRoot g f :=
  earlyFinalRoot g f
    (ForwardQAmbientFibreFrame.ambientAtSourceRoot g v)
    (ForwardQAmbientFibreFrame.source_root_before_cut g v)

/-- ANY assignment to all final roots restricts canonically
to an assignment to the genuine old source variables. -/
noncomputable def sourceAssignmentOfFinal
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (σ : FinalRoot g f → α) :
    g.core.source.word.Vars → α :=
  fun v => σ (oldSourceFinalRoot g f v)

/-- Under the no-extra-root hypothesis, any retained FINAL root
can be identified with an actual old-source variable at the SAME
bounded ambient root. Keep this witness in Prop before using choice:
a proof of existence cannot be eliminated directly into a Type. -/
theorem existsOldVariableAtEarlyFinalRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (hret : RetainedRootsAreOld g)
    (r : FinalRoot g f)
    (hbefore : ForwardAux r.1.1 g.core.cut) :
    ∃ v : g.core.source.word.Vars, v.1 = r.1 := by
  have hT : r.1.1 ∈ g.core.T :=
    (g.ambient_support_T r.1).1
      (boundedFinalRoots_subset_original g f r)
  have hr : r.1.1 ∈ retained g.core := by
    unfold retained
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hT,hbefore⟩
  have hsource :
      r.1.1 ∈ g.core.source.word.supportNodes :=
    hret r.1.1 hr
  change r.1.1 ∈
    g.core.source.word.support.map (fun v => v.1) at hsource
  rcases List.mem_map.mp hsource with ⟨v,hv,hval⟩
  exact ⟨⟨v,hv⟩, Subtype.ext hval⟩

/-- Recover the uniquely determined source variable by its root. -/
noncomputable def oldVariableAtEarlyFinalRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (hret : RetainedRootsAreOld g)
    (r : FinalRoot g f)
    (hbefore : ForwardAux r.1.1 g.core.cut) :
    g.core.source.word.Vars :=
  Classical.choose
    (existsOldVariableAtEarlyFinalRoot g f hret r hbefore)

/-- The recovered old variable has exactly the retained final
root, not just an auxiliary decoder with equivalent evaluations. -/
theorem oldVariableAtEarlyFinalRoot_val
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (hret : RetainedRootsAreOld g)
    (r : FinalRoot g f)
    (hbefore : ForwardAux r.1.1 g.core.cut) :
    (oldVariableAtEarlyFinalRoot g f hret r hbefore).1 = r.1 :=
  Classical.choose_spec
    (existsOldVariableAtEarlyFinalRoot g f hret r hbefore)

/-- With no extra retained roots, anchoring the old assignment
obtained from sigma leaves the ENTIRE final assignment unchanged.
New projected variable values remain independent, as before. -/
theorem anchoredAssignment_of_final_eq
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (hret : RetainedRootsAreOld g)
    (σ : FinalRoot g f → α) :
    anchoredAssignment g f
      (sourceAssignmentOfFinal g f σ) σ = σ := by
  funext r
  by_cases hbefore : ForwardAux r.1.1 g.core.cut
  · let v := oldVariableAtEarlyFinalRoot
      g f hret r hbefore
    have hval : v.1 = r.1 :=
      oldVariableAtEarlyFinalRoot_val g f hret r hbefore
    have hOrig :
        (⟨r.1,boundedFinalRoots_subset_original g f r⟩ :
          g.ambient.Vars) =
        ForwardQAmbientFibreFrame.ambientAtSourceRoot g v := by
      apply Subtype.ext
      exact hval.symm
    have hSub :
        g.substitution
          (⟨r.1,boundedFinalRoots_subset_original g f r⟩ :
            g.ambient.Vars) = Sum.inr v := by
      rw [hOrig]
      exact ForwardQAmbientFibreFrame.source_substitution_fixes_old_root
        g v
    have hFinal : oldSourceFinalRoot g f v = r := by
      apply Subtype.ext
      exact hval
    change (if h : ForwardAux r.1.1 g.core.cut then
      SpanAudit.evalSymbol (sourceAssignmentOfFinal g f σ)
        (g.substitution
          ⟨r.1,boundedFinalRoots_subset_original g f r⟩)
      else σ r) = σ r
    simp [hbefore, hSub, SpanAudit.evalSymbol,
      sourceAssignmentOfFinal, hFinal]
  · simp [anchoredAssignment,hbefore]

/-- Under retained-root equality, EVERY assignment sigma to the complete
final f' roots is represented by an actual corrected starred mixed-span
point and an evaluation of the old source variables. -/
theorem every_final_assignment_has_actual_starred_Q_witness
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (hret : RetainedRootsAreOld g)
    (σ : FinalRoot g f → α) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ =
      (interpolatedFinalWord
        g f (fun x : α => x) fallback).eval σ := by
  let τ := sourceAssignmentOfFinal g f σ
  refine ⟨liftedStarred g.core fallback
      (ForwardQFinalInducedStarredPoint.inducedStarredInput
        g f fallback σ hq),τ,?_⟩
  have hEq :=
    ForwardQFinalWholeDomainEvaluation.inducedFibreQ_eval_eq_final_eval
      hb g f fallback τ σ hq
  have hAnchor : anchoredAssignment g f τ σ = σ :=
    anchoredAssignment_of_final_eq g f hret σ
  rw [hAnchor] at hEq
  exact hEq

/-- Reverse coverage of the ENTIRE final evaluated span, using
ACTUAL corrected starred Q inputs, follows from and does not hide
the retained-root support equality hypothesis. -/
theorem every_final_span_word_has_actual_starred_Q_witness
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (hret : RetainedRootsAreOld g) :
    ∀ ψ : TreeWord b n α,
      ψ ∈ (interpolatedFinalWord
        g f (fun x : α => x) fallback).span →
      ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback)
        (τ : g.core.source.word.Vars → α),
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w).word.eval τ = ψ := by
  intro ψ hψ
  obtain ⟨σ,hσ⟩ := hψ
  obtain ⟨w,τ,hEq⟩ :=
    every_final_assignment_has_actual_starred_Q_witness
      hb g f fallback hq hret σ
  exact ⟨w,τ,hEq.trans hσ⟩

/-- The relevant *unrestricted* reverse coverage property,
allowing even unstarred enlarged inputs. This is weaker than
covering by genuine corrected starred W_* images. -/
def HasReverseQCoverage
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α) : Prop :=
  ∀ ψ : TreeWord b n α,
    ψ ∈ (interpolatedFinalWord
      g f (fun x : α => x) fallback).span →
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
      (τ : g.core.source.word.Vars → α),
      SpanAudit.eval
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w) τ = ψ

/-- Under positive branching and local height, a two-letter alphabet
makes the current corrected f' reverse-coverage statement EQUIVALENT
to having no extra retained early ambient roots. The reverse
implication uses a genuine corrected starred W_* witness; the forward
implication uses the exhaustive constant-or-collapsed-root obstruction. -/
theorem hasReverseQCoverage_iff_retainedRootsAreOld
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (hα : SpanAudit.HasTwoLetters α) :
    HasReverseQCoverage g f fallback ↔ RetainedRootsAreOld g := by
  constructor
  · intro hcover t ht
    by_contra hnot
    let u := ForwardQAmbientFibreFrame.ambientAtTRoot
      g t (retained_subset_T g.core t ht)
    have hu : ForwardAux u.1.1 g.core.cut :=
      (Finset.mem_filter.mp ht).2
    have hnotold : u.1 ∉ g.core.source.word.support := by
      intro hs
      have hmem : t ∈ g.core.source.word.supportNodes := by
        change t ∈ g.core.source.word.support.map (fun v => v.1)
        exact List.mem_map.mpr ⟨u.1,hs,rfl⟩
      exact hnot hmem
    obtain ⟨ψ,hψ,hmiss⟩ :=
      ForwardQFinalExtraRetainedObstruction.not_every_final_evaluation_of_extra_retained_root
        g f fallback hα u hu hnotold
    obtain ⟨w,τ,heq⟩ := hcover ψ hψ
    exact hmiss w τ heq
  · intro hret ψ hψ
    obtain ⟨w,τ,heq⟩ :=
      every_final_span_word_has_actual_starred_Q_witness
        hb g f fallback hq hret ψ hψ
    refine ⟨w.1,τ,?_⟩
    exact heq

/-- The elementary cardinal condition l <= m is incompatible with
full reverse Q coverage for this corrected final-support construction.
This is a consequence of the exact coverage criterion, not a new
hypothesis on an arbitrary source substitution rho. -/
theorem not_hasReverseQCoverage_of_l_le_cut_rank
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (hα : SpanAudit.HasTwoLetters α)
    (hlm : l ≤ m) :
    ¬ HasReverseQCoverage g f fallback := by
  intro hcover
  have hret : RetainedRootsAreOld g :=
    (hasReverseQCoverage_iff_retainedRootsAreOld
      hb g f fallback hq hα).1 hcover
  obtain ⟨t,ht,hnotold⟩ :=
    ForwardQFinalRetainedCardinality.exists_extra_retained_of_l_le_cut_rank
      g.core hlm
  exact hnotold (hret t ht)

end DualTree.ForwardQFinalReverseCoverageCriterion
