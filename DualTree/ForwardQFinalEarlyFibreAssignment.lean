import DualTree.ForwardQFinalWholeFibreQEvaluation
import DualTree.ForwardQFinalSupportCut

/-!
# Early original-f-fibres: the necessary source-assignment compatibility

The actual corrected fibrewise Q does NOT interpolate arbitrary
assignments to the retained original f roots: on early fibres it
uses the fixed source refinement g' = f[rho]. It would therefore
be false to claim Q(x_sigma) and eval(f',sigma) agree there for
EVERY independently chosen sigma.

Instead, given an assignment tau to the OLD source variables and
an arbitrary assignment sigma0 to the final variables, change
sigma0 only on retained (at/before-cut) roots so that those
values are exactly the evaluation of rho under tau.
No new projected variable is changed, because its root lies
strictly OUTSIDE the forward auxiliary cut.

For this anchored assignment:
* any original ambient f-constant is preserved by Q and f';
* on every early original ambient f-fibre, evaluating the
  actual fibrewise Q-word under tau equals evaluating f' under
  the anchored final-variable assignment;
* on safe late projected fibres the previously verified
  Q/f' equality holds for ANY assignment and hence also this
  anchored one.

This is an honest conditional/existential alignment. It does
NOT assert whole-word equality at unsafe fibres, arbitrary
early assignments, or equivalence to the paper's reverse W_*.
-/

namespace DualTree.ForwardQFinalEarlyFibreAssignment

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalWholeFibreQEvaluation

/-- Any original f-variable root at/before the forward cut
belongs to the genuine rank-filtered final support, as a
bounded variable root with its original identity. -/
noncomputable def earlyFinalRoot
    {b n l k m q : Nat} {α : Type*}
    {β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    FinalRoot g f := by
  have htT : u.1.1 ∈ g.core.T :=
    (g.ambient_support_T u.1).1 u.2
  have hret : u.1.1 ∈ retained g.core := by
    unfold retained
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr htT,hbefore⟩
  have hfinal : u.1.1 ∈ finalBudgetSupport g.core f (m+q) :=
    Finset.mem_union.mpr (Or.inl hret)
  exact ⟨u.1,(mem_boundedFinalRoots_iff g f u.1).2 hfinal⟩

/-- The early-root constructor has precisely the same bounded
ambient node as its original f-variable argument. -/
theorem earlyFinalRoot_val
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    (earlyFinalRoot g f u hbefore).1 = u.1 := rfl

/-- The verified global substitution fixes every early original
f-variable root as an independent retained final root. -/
theorem globalRootSymbol_early
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    globalRootSymbol g f decode fallback u =
      Sum.inr (earlyFinalRoot g f u hbefore) := by
  have horig :
      (⟨(earlyFinalRoot g f u hbefore).1,
        boundedFinalRoots_subset_original g f
          (earlyFinalRoot g f u hbefore)⟩ :
        g.ambient.Vars) = u :=
    Subtype.ext (earlyFinalRoot_val g f u hbefore)
  have hfix :=
    globalRootSymbol_fixes_final_root g f decode fallback
      (earlyFinalRoot g f u hbefore)
  rw [horig] at hfix
  exact hfix

/-- Anchor only EARLY selected final-root values to the
old source substitution rho evaluated under tau. Else keep
the independently specified base assignment sigma0. -/
noncomputable def anchoredAssignment
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α) :
    FinalRoot g f → α :=
  fun v =>
    if ForwardAux v.1.1 g.core.cut then
      SpanAudit.evalSymbol τ
        (g.substitution
          ⟨v.1,boundedFinalRoots_subset_original g f v⟩)
    else σ0 v

/-- On any early original f-root u, the anchored global
assignment evaluates the actual total ambient substitution
to the very same value as the source rho under tau. -/
theorem anchoredAssignment_early
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    SpanAudit.evalSymbol (anchoredAssignment g f τ σ0)
      (globalRootSymbol g f decode fallback u) =
      SpanAudit.evalSymbol τ (g.substitution u) := by
  rw [globalRootSymbol_early g f decode fallback u hbefore]
  change anchoredAssignment g f τ σ0
    (earlyFinalRoot g f u hbefore) =
      SpanAudit.evalSymbol τ (g.substitution u)
  have horig :
      (⟨(earlyFinalRoot g f u hbefore).1,
        boundedFinalRoots_subset_original g f
          (earlyFinalRoot g f u hbefore)⟩ :
        g.ambient.Vars) = u :=
    Subtype.ext (earlyFinalRoot_val g f u hbefore)
  simp [anchoredAssignment,
    earlyFinalRoot_val g f u hbefore,hbefore,horig]

/-- Anchoring does not change the values of any new selected
projected variable P_i(z): all such roots are beyond cut.
Thus the independently chosen local Ramsey variables remain
independent when the old source variables are synchronized. -/
theorem anchoredAssignment_projected
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (u : SelectedTag g f) :
    anchoredAssignment g f τ σ0
      (selectedBoundedRoot g f u) =
      σ0 (selectedBoundedRoot g f u) := by
  have hafter :
      ¬ ForwardAux (selectedBoundedRoot g f u).1.1
        g.core.cut := by
    rw [selectedBoundedRoot_node]
    exact projected_outside_cut g.core u.1
  simp [anchoredAssignment,hafter]

/-- The actual corrected fibrewise Q evaluated under the old
source assignment tau agrees on the ENTIRE early original
ambient f-fibre with f' evaluated under the anchored assignment.
The early-fibre compatibility is PROVED, not silently assumed. -/
theorem inducedFibreQ_eval_on_early_fibre
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (hq : 0 < q)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    SpanAudit.evalSymbol τ
      ((inducedFibreQ hb g f fallback
        (anchoredAssignment g f τ σ0) hq).word.word s) =
    SpanAudit.evalSymbol (anchoredAssignment g f τ σ0)
      ((interpolatedFinalWord g f (fun a : α => a) fallback).word s) := by
  have hQ :
      (inducedFibreQ hb g f fallback
        (anchoredAssignment g f τ σ0) hq).word.word s =
        g.core.source.word.word s := by
    change ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
      (liftedStarred g.core fallback
        (ForwardQFinalInducedStarredPoint.inducedStarredInput g f
          fallback (anchoredAssignment g f τ σ0) hq)).1 s =
      g.core.source.word.word s
    exact ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback _ s u hs hbefore
  have hsource : g.core.source.word.word s =
      g.substitution u := by
    rw [g.source_substitution]
    simp [SpanAudit.substitute,hs]
  have hfinal :
      (interpolatedFinalWord g f (fun a : α => a) fallback).word s =
        globalRootSymbol g f (fun a : α => a) fallback u := by
    change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f (fun a : α => a) fallback) s = _
    simp [SpanAudit.substitute,hs]
  rw [hQ,hsource,hfinal]
  exact (anchoredAssignment_early g f (fun a : α => a)
    fallback τ σ0 u hbefore).symm

/-- At any original ambient f-CONSTANT, actual corrected Q
and final f' evaluations agree for ALL assignments, with
no early compatibility restriction. -/
theorem inducedFibreQ_eval_on_ambient_constant
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (τ : g.core.source.word.Vars → α)
    (s : BoundedNode b n)
    (a : α)
    (hs : g.ambient.word s = Sum.inl a) :
    SpanAudit.evalSymbol τ
      ((inducedFibreQ hb g f fallback σ hq).word.word s) =
    SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f (fun a : α => a) fallback).word s) := by
  have hQ :
      (inducedFibreQ hb g f fallback σ hq).word.word s =
        Sum.inl a := by
    change ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
      (liftedStarred g.core fallback
        (ForwardQFinalInducedStarredPoint.inducedStarredInput g f
          fallback σ hq)).1 s = Sum.inl a
    exact ForwardQAmbientFibreSymbol.fibreQ_original_constant
      g fallback _ s a hs
  have hF :
      (interpolatedFinalWord g f (fun a : α => a) fallback).word s =
        Sum.inl a := by
    change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f (fun a : α => a) fallback) s = Sum.inl a
    simp [SpanAudit.substitute,hs]
  simp [hQ,hF,SpanAudit.evalSymbol]

end DualTree.ForwardQFinalEarlyFibreAssignment
