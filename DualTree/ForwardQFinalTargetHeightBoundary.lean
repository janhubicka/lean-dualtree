import DualTree.ForwardQFinalSyntacticSpanTransfer

/-!
# A necessary height allowance for fixed-signature targets

Nonemptiness of the final word's evaluated span does not imply that it
admits a starred target with the prescribed complete signature. At local
height one the final support has height `m+1`, while the retained cut has
intrinsic rank `m`. It therefore has no strict descendant in that support.
A target with the same complete signature must have that cut as an
interior vertex, so its tree cannot be contained in the final support.

Consequently a positive local height permitting such a target must be at
least two. This is only a necessary condition. No existence theorem for
targets at larger heights, and no emptiness of the final evaluated word
span, is asserted.
-/

namespace DualTree.ForwardQFinalTargetHeightBoundary

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalSyntacticSpanTransfer

/-- At local height one, the retained cut has maximal final intrinsic
rank and cannot have a strict descendant in the exact final support.
This geometric fact is independent of all word constants. -/
theorem cut_has_no_strict_descendant_at_local_height_one
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c 1 β)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f (m+1)) :
    ¬ IsStrictPrefix c.cut t := by
  intro hstrict
  have hret : c.cut ∈ retained c := cut_mem_retained c
  have hcutFinal : c.cut ∈ finalBudgetSupport c f (m+1) := by
    change c.cut ∈ retained c ∪ selectedProjectedRoots c f (m+1)
    exact Finset.mem_union.mpr (Or.inl hret)
  have hcutRank :
      SkewTree.heightAt (finalBudgetSupport c f (m+1)).toList c.cut = m :=
    (ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f (m+1) c.cut hret).trans c.hm
  have hgrowth := SupportHeightRanks.heightAt_lt_of_strictPrefix
    (finalBudgetSupport c f (m+1)).toList
    (Finset.mem_toList.mpr hcutFinal) hstrict
  have hbound := ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
    c f (m+1) (Nat.lt_succ_self m) t ht
  rw [hcutRank] at hgrowth
  omega

/-- Local height one allows no source-relative starred target: complete
signature equality forces the retained cut to be interior in the target,
whereas the final support has no strict descendant of that cut. -/
theorem no_sourceRelativeTarget_at_local_height_one
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core 1 (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    ¬ SourceRelativeTarget hb g
      (enlargedInterpolatedFinalWord g f fallback) O := by
  rintro ⟨cutO, H, _hRef, hTree⟩
  have hcutEq : cutO = g.core.cut :=
    ForwardQFinalFullSignature.complete_signature_forces_same_cut
      hb g O cutO H
  have hInterior : g.core.cut ∈ SkewTree.interior O.tree :=
    hcutEq ▸ H.cutInterior
  apply (Lemma27QTerminal.not_interior_of_no_strict_descendant
    O.tree g.core.cut ?_) hInterior
  intro t ht
  have hFinal : t ∈ finalBudgetSupport g.core f (m+1) :=
    (enlargedInterpolatedFinalWord_supportNodes_iff
      g f fallback t).1 (hTree t ht)
  exact cut_has_no_strict_descendant_at_local_height_one g.core f t hFinal

/-- The fixed-signature target class is empty at local height one,
although the genuine complete final word still has evaluated words. -/
theorem no_sourceRelativeTarget_exists_at_local_height_one
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core 1 (Sum α (Fin (m+1))))
    (fallback : α) :
    ¬ ∃ O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)),
      SourceRelativeTarget hb g
        (enlargedInterpolatedFinalWord g f fallback) O := by
  rintro ⟨O, hO⟩
  exact no_sourceRelativeTarget_at_local_height_one hb g f fallback O hO

/-- An actual source-relative starred target at positive local height
requires at least two local support levels. This necessary bound does
not claim that height two suffices to construct such a target. -/
theorem sourceRelativeTarget_requires_two_local_levels
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq : 0 < q)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : SourceRelativeTarget hb g
      (enlargedInterpolatedFinalWord g f fallback) O) :
    1 < q := by
  by_contra hnot
  have hqOne : q = 1 := by omega
  subst q
  exact no_sourceRelativeTarget_at_local_height_one hb g f fallback O hO

end DualTree.ForwardQFinalTargetHeightBoundary
