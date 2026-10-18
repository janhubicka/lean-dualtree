import DualTree.ForwardQFinalEarlyFibreAssignment
import DualTree.ForwardInverseConeTails
import DualTree.ForwardQFibreDefaults

/-!
# Late original ambient f-fibres with NO shortened safe local address

An original ambient f-root can lie after the corrected forward cut
but outside the image of every certified shortened frontier cone.
Both the true fibrewise Q word and the constructed interpolating
ambient f' must emit the fallback CONSTANT on that entire f-fibre.

The key geometric lemma proves the CONTRAPOSITIVE: whenever an
original f-root has a selected frontier and its inverse-address
suffix lies in the common shortened local domain, it is exactly
P_i(z) for the genuine sorted frontier index i and suffix z.
This uses the already certified inverse-address cone-surjectivity,
not a guessed inverse or an assumption of final skewness.

Consequently safeAddress = none and being post-cut imply:
* the original ambient root does not belong to final f' support;
* the interpolating global substitution emits fallback;
* the actual corrected fibrewise Q emits the SAME fallback
  throughout its entire original f-fibre;
* any evaluations of Q and f' agree there.

This closes the genuinely late unsafe/no-frontier case. The
paper's printed reverse-starred domain is still different.
-/

namespace DualTree.ForwardQFinalUnsafeFibreFallback

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalSafeAddressLookup
open ForwardQFinalWholeFibreQEvaluation

/-- Every original ambient f-root with an actual selected frontier
and a SAFE canonical inverse tail is in the image of the genuine
shortened projection. Its partial decoder returns that exact
frontier and local address. -/
theorem safeAddress_some_of_safe_frontier
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (u : g.ambient.Vars)
    (i : Index g.core)
    (hsel : ForwardQFullFrontierWord.selectedFrontier
      g.core u.1 = some i)
    (hsafe : InHomTree (k-(m+1))
      (ForwardQActualCoordinateWord.tailOfTNode g.core i
        ⟨u.1.1,(g.ambient_support_T u.1).1 u.2⟩)) :
    ∃ z : BoundedNode b (k-(m+1)),
      safeAddress g.core u.1.1 = some (⟨i,z⟩ : LocalAddress g.core) := by
  let target : {t : Node b // t ∈ g.core.T} :=
    ⟨u.1.1,(g.ambient_support_T u.1).1 u.2⟩
  let frontier := ForwardOrderedProjections.frontierAt
    g.core.T g.core.cut i
  have hprefix : IsPrefix frontier.1 target.1 :=
    ForwardQAmbientFibreSymbol.selectedFrontier_some_prefix
      g.core u.1 i hsel
  have htail :
      (ForwardQActualCoordinateWord.tailOfTNode
        g.core i target).length < k-(m+1) := hsafe
  have hbudget :
      SkewTree.heightAt g.core.T target.1 -
      SkewTree.heightAt g.core.T frontier.1 < k-(m+1) := by
    unfold ForwardQActualCoordinateWord.tailOfTNode at htail
    simp only [List.length_drop] at htail
    rw [ForwardCompleteBijection.inverse_length
          g.core.T g.core.hcomplete g.core.hnon target,
        ForwardCompleteBijection.inverse_length
          g.core.T g.core.hcomplete g.core.hnon frontier] at htail
    exact htail
  let z : BoundedNode b (k-(m+1)) :=
    ⟨ForwardQActualCoordinateWord.tailOfTNode
      g.core i target,hsafe⟩
  have hz :
      ForwardInverseConeTails.relativeTail
        g.core.T g.core.hcomplete g.core.hnon
        frontier target hprefix hbudget = z := by
    apply Subtype.ext
    rfl
  have hreach :=
    ForwardInverseConeTails.projectCommon_reaches_target
      g.core.T g.core.hcomplete g.core.hnon
      g.core.cut g.core.hcutT g.core.hm
      frontier target
      (ForwardOrderedProjections.frontierAt_spec
        g.core.T g.core.cut i) hprefix hbudget
  rw [hz] at hreach
  have hnode :
      (projected g.core ⟨i,z⟩).1 = u.1.1 :=
    congrArg Subtype.val hreach
  refine ⟨z,?_⟩
  simpa only [hnode] using
    (safeAddress_projected g.core ⟨i,z⟩)

/-- A post-cut original f-variable root with NO safe address
cannot be one of the final selected roots: retained roots
lie before cut, and selected projections have exact
safeAddress preimages. -/
theorem not_final_root_of_late_no_safe
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    u.1 ∉ boundedFinalRoots g f := by
  intro hroot
  have hfinal : u.1.1 ∈ finalBudgetSupport g.core f (m+q) :=
    (mem_boundedFinalRoots_iff g f u.1).1 hroot
  change u.1.1 ∈
    retained g.core ∪ selectedProjectedRoots g.core f (m+q)
    at hfinal
  rcases Finset.mem_union.mp hfinal with hret | hnew
  · exact hafter (Finset.mem_filter.mp hret).2
  · obtain ⟨v,_htag,heq,_budget⟩ :=
      selectedProjectedRoots_budget_witness
        g.core f (m+q) u.1.1 hnew
    have hsome := safeAddress_projected g.core v
    rw [heq] at hnone
    rw [hnone] at hsome
    cases hsome

/-- The genuine global f' substitution constantizes every
original ambient f root that is both late and outside the
certified safe projection image, with no fabricated final name. -/
theorem globalRootSymbol_late_no_safe
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    globalRootSymbol g f decode fallback u = Sum.inl fallback := by
  have hnot : u.1 ∉ boundedFinalRoots g f :=
    not_final_root_of_late_no_safe g f u hafter hnone
  simp [globalRootSymbol,hnone,hnot]

/-- At a late original f-variable fibre whose root has NO
safe local address, the ACTUAL fibrewise Q symbol is the
fallback alphabet constant. This holds at EVERY position
of that f-fibre, not merely at the root. -/
theorem inducedFibreQ_symbol_late_no_safe
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    (inducedFibreQ hb g f fallback σ hq).word.word s =
      Sum.inl fallback := by
  let w := liftedStarred g.core fallback
    (ForwardQFinalInducedStarredPoint.inducedStarredInput
      g f fallback σ hq)
  have hlate :=
    ForwardQAmbientFibreSymbol.fibreQ_after_cut
      g fallback w.1 s u hs hafter
  change ForwardQAmbientFibreSymbol.fibreQSymbol
    g fallback w.1 s = Sum.inl fallback
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
          safeAddress_some_of_safe_frontier g u i hsel hsafe
        rw [hnone] at hsome
        cases hsome
      exact
        ForwardQFibreDefaults.decodeAmbientRoot_unsafe_fallback
          g fallback w.1 u i hsel hunsafe

/-- For every late original f-fibre without a safe projected
address, evaluations of actual corrected Q and of the
interpolating final ambient word agree unconditionally:
both are the SAME fallback constant. -/
theorem inducedFibreQ_eval_late_no_safe
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (τ : g.core.source.word.Vars → α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    SpanAudit.evalSymbol τ
      ((inducedFibreQ hb g f fallback σ hq).word.word s) =
    SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f (fun a : α => a) fallback).word s) := by
  have hQ :
      (inducedFibreQ hb g f fallback σ hq).word.word s =
        Sum.inl fallback :=
    inducedFibreQ_symbol_late_no_safe
      hb g f fallback σ hq u s hs hafter hnone
  have hsub : globalRootSymbol
      g f (fun a : α => a) fallback u = Sum.inl fallback :=
    globalRootSymbol_late_no_safe
      g f (fun a : α => a) fallback u hafter hnone
  have hF :
      (interpolatedFinalWord g f (fun a : α => a) fallback).word s =
        Sum.inl fallback := by
    change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f (fun a : α => a) fallback) s =
        Sum.inl fallback
    simp [SpanAudit.substitute,hs,hsub]
  simp [hQ,hF,SpanAudit.evalSymbol]

end DualTree.ForwardQFinalUnsafeFibreFallback
