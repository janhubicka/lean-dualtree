import DualTree.ForwardQFinalTargetExistence

/-!
# Sharp support threshold for actual induced Q images

The enlarged local mixed span has a genuine induced starred input at
every positive local height. Nevertheless, its corrected Q image can be
an eligible target of the final interpolation only when q >= 2.

This module proves a stronger, pointwise geometric result: for EACH
assignment to the final roots, the ENTIRE induced Q tree is contained
in the actual final support if and only if q >= 2. At local height
one this yields a genuine starred input IN the mixed span whose Q
tree has a node OUTSIDE the final support.

The proof uses the already checked set-valued full signature and
syntactic-refinement laws, rather than assuming coverage or nonempty
targets. It does not construct a local Ramsey witness.
-/

namespace DualTree.ForwardQFinalInducedSupportThreshold

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQAmbientFibreLegalWord
open ForwardQFinalSetSpanTransfer

/-- For each genuine induced input, eligibility of its actual corrected
Q output is equivalent to the sharp two-level height budget. All
assignments, auxiliary constants, and singleton alphabets are included. -/
theorem inducedQ_sourceRelativeSetTarget_iff_two_le
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    SourceRelativeSetTarget hb g
      (enlargedInterpolatedFinalWord g f fallback)
      (fibreQStarredWord hb g fallback
        (enlargedInducedStarredInput g f fallback σ hq))
       ↔ 2 ≤ q := by
  constructor
  · intro hTarget
    have hTwo :=
      ForwardQFinalTargetHeightBoundary.sourceRelativeSetTarget_requires_two_local_levels
        hb g f fallback hq
        (fibreQStarredWord hb g fallback
          (enlargedInducedStarredInput g f fallback σ hq)) hTarget
    omega
  · intro hTwo
    exact ForwardQFinalTargetExistence.inducedQ_sourceRelativeSetTarget
      hb g f fallback σ hq hTwo

/-- The exact GEOMETRIC threshold, not merely a target-existence
statement: no arbitrary choice of final-root letters repairs the missing
Q terminal at positive local height one. -/
theorem inducedQ_tree_subset_final_iff_two_le
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    (∀ t : Node b,
      t ∈ (fibreQStarredWord hb g fallback
        (enlargedInducedStarredInput g f fallback σ hq)).tree →
      t ∈ (enlargedInterpolatedFinalWord g f fallback).supportNodes)
       ↔ 2 ≤ q := by
  constructor
  · intro hTree
    have hTarget : SourceRelativeSetTarget hb g
        (enlargedInterpolatedFinalWord g f fallback)
        (fibreQStarredWord hb g fallback
          (enlargedInducedStarredInput g f fallback σ hq)) :=
      ⟨g.core.cut,
        ForwardQFinalInducedSignature.fibreQStarredWord_sameCompleteSetForwardSignature
          hb g fallback _,
        ForwardQFinalInducedRefinement.inducedQ_syntacticallyRefines_final
          hb g f fallback σ hq,
        hTree⟩
    exact (inducedQ_sourceRelativeSetTarget_iff_two_le
      hb g f fallback σ hq).1 hTarget
  · intro hTwo
    exact ForwardQFinalInducedSupport.fibreQStarredWord_enlargedInduced_tree_subset_finalWordSupport
      hb g f fallback σ hq hTwo

/-- Every induced Q tree contains a node outside the final word's
support precisely at the excluded positive local height q=1. -/
theorem inducedQ_tree_has_unsupported_node_iff_q_one
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    (∃ t : Node b,
      t ∈ (fibreQStarredWord hb g fallback
        (enlargedInducedStarredInput g f fallback σ hq)).tree ∧
      t ∉ (enlargedInterpolatedFinalWord g f fallback).supportNodes)
       ↔ q = 1 := by
  classical
  constructor
  · rintro ⟨t, ht, hnot⟩
    have hnotTwo : ¬ 2 ≤ q := by
      intro hTwo
      exact hnot
        ((inducedQ_tree_subset_final_iff_two_le
          hb g f fallback σ hq).2 hTwo t ht)
    omega
  · intro hOne
    by_contra hNo
    have hSubset : ∀ t : Node b,
        t ∈ (fibreQStarredWord hb g fallback
          (enlargedInducedStarredInput g f fallback σ hq)).tree →
        t ∈ (enlargedInterpolatedFinalWord g f fallback).supportNodes := by
      intro t ht
      by_contra hNot
      exact hNo ⟨t, ht, hNot⟩
    have hTwo := (inducedQ_tree_subset_final_iff_two_le
      hb g f fallback σ hq).1 hSubset
    omega

/-- The height-one obstruction is NONVACUOUS: a real corrected-starred
input lies in the actual supplied mixed span, but its Q image has a
node outside the final support. This does NOT assert the mixed span is
empty and does NOT prohibit the complete final word's evaluated span. -/
theorem height_one_mixed_span_has_unsupported_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core 1 (Sum α (Fin (m+1))))
    (fallback : α) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback,
      w.1 ∈ f.span ∧
      ∃ t : Node b,
        t ∈ (fibreQStarredWord hb g fallback w).tree ∧
        t ∉ (enlargedInterpolatedFinalWord g f fallback).supportNodes := by
  let σ : FinalRoot g f → α := fun _ => fallback
  let w := enlargedInducedStarredInput g f fallback σ (by decide : 0 < 1)
  refine ⟨w, enlargedInducedStarredInput_mem_span
    g f fallback σ (by decide : 0 < 1), ?_⟩
  exact (inducedQ_tree_has_unsupported_node_iff_q_one
    hb g f fallback σ (by decide : 0 < 1)).2 rfl

end DualTree.ForwardQFinalInducedSupportThreshold
