import DualTree.ForwardQFinalProjectedPredecessorCount

/-!
# Exact intrinsic height in the corrected final Lemma 27 support

The rank-budgeted post-Ramsey final ambient support T'_M
contains the retained initial T prefix and the image under
P_i of selected local component variable roots. These two
sets are disjoint. We have already proved two independent
cardinality identities for the predecessors of P_i(z):

  (1) retained strict predecessors contribute h_T(frontier_i);
  (2) selected projected strict predecessors contribute
      h_ws(f_i)(z), provided the local root z itself passes
      the exact target-M filter.

This module performs the DISJOINT UNION calculation for the
genuine intrinsic rank heightAt(T'_M), yielding the formula

  h_(T'_M)(P_i(z)) =
    h_T(frontier_i) + h_ws(f_i)(z).

The printed target-height filter then proves all SELECTED
projected vertices have intrinsic T'_M rank STRICTLY below M.
All retained vertices already retain their ambient T ranks.

The full assertion that T'_M is M-COMPLETE SKEW is NOT
discharged merely by this calculation. Full branching,
the auxiliary length order across equal levels, and
crossing retained/projected ranks remain to be validated.
Neither the final ambient variable word f' nor the
Ramsey step is asserted here.
-/

namespace DualTree.ForwardQFinalIntrinsicRank

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalBudgetPredecessors
open ForwardQFinalRetainedRanks
open ForwardQFinalSelectedPredecessors
open ForwardQFinalProjectedPredecessorCount

/-- A retained vertex is a proper prefix of a new projected
root P_i(z) precisely when it is a proper T prefix of the
genuine minimal outside-cut frontier of i. This is the
exact filter identity used for the old rank contribution. -/
theorem retained_projected_predecessor_filter_eq_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)) =
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true)) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hret,hpreB⟩ := Finset.mem_filter.mp hs
    have hpre : IsStrictPrefix s (projected c ⟨i,z⟩).1 :=
      (SkewBranchGeometry.strictPrefixB_iff _ _).1 hpreB
    have hfront : IsPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
      (retained_strictPrefix_projected_iff
        c ⟨i,z⟩ s hret).1 hpre
    have hstrictFront : IsStrictPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
      (T_predecessor_frontier_iff_retained c i s
        (retained_subset_T c s hret)).2
        ⟨hret,hfront⟩
    exact Finset.mem_filter.mpr
      ⟨hret,
        (SkewBranchGeometry.strictPrefixB_iff _ _).2
          hstrictFront⟩
  · intro hs
    obtain ⟨hret,hpreB⟩ := Finset.mem_filter.mp hs
    have hfront : IsStrictPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
      (SkewBranchGeometry.strictPrefixB_iff _ _).1 hpreB
    have hpre : IsStrictPrefix s (projected c ⟨i,z⟩).1 :=
      (retained_strictPrefix_projected_iff
        c ⟨i,z⟩ s hret).2 hfront.1
    exact Finset.mem_filter.mpr
      ⟨hret,(SkewBranchGeometry.strictPrefixB_iff _ _).2 hpre⟩

/-- The true predecessor filter of the rank-budgeted
support splits into the union of its old retained filter
and its selected new projected filter. -/
theorem final_projected_predecessor_filter_union
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    ((finalBudgetSupport c f M).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)) =
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)) ∪
    ((selectedProjectedRoots c f M).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)) := by
  classical
  simp only [finalBudgetSupport, Finset.filter_union]

/-- The two predecessor filters are DISJOINT because the
underlying retained and selected projected sets are disjoint. -/
theorem final_projected_predecessor_filters_disjoint
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    Disjoint
      ((retained c).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true))
      ((selectedProjectedRoots c f M).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hsOld hsNew
  exact (Finset.disjoint_left.mp
    (finalBudgetSupport_disjoint_retained c f M))
      (Finset.mem_filter.mp hsOld).1
      (Finset.mem_filter.mp hsNew).1

/-- The intrinsic rank of every genuine projected local
variable root selected by the exact final target-M filter
is the sum of the original frontier rank in T and the
intrinsic local variable-support rank of its address. -/
theorem final_projected_height_formula
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 =
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 := by
  classical
  have hOld :
      ((retained c).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true)).card =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
    calc
      ((retained c).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true)).card =
        ((retained c).filter
          (fun s => SkewTree.strictPrefixB s
            (ForwardOrderedProjections.frontierAt
              c.T c.cut i).1 = true)).card :=
          congrArg Finset.card
            (retained_projected_predecessor_filter_eq_frontier
              c i z)
      _ = SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt
            c.T c.cut i).1 :=
          (frontier_rank_eq_retained_predecessor_card c i).symm
  have hNew :
      ((selectedProjectedRoots c f M).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true)).card =
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 :=
    selected_projected_predecessor_card_eq_local_height
      c f M i z hz
  calc
    SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 =
      ((finalBudgetSupport c f M).filter
        (fun s => SkewTree.strictPrefixB s
          (projected c ⟨i,z⟩).1 = true)).card :=
      heightAt_finset_eq_card (finalBudgetSupport c f M) _
    _ = (((retained c).filter
          (fun s => SkewTree.strictPrefixB s
            (projected c ⟨i,z⟩).1 = true)) ∪
        ((selectedProjectedRoots c f M).filter
          (fun s => SkewTree.strictPrefixB s
            (projected c ⟨i,z⟩).1 = true))).card :=
      congrArg Finset.card
        (final_projected_predecessor_filter_union c f M i z)
    _ = ((retained c).filter
          (fun s => SkewTree.strictPrefixB s
            (projected c ⟨i,z⟩).1 = true)).card +
        ((selectedProjectedRoots c f M).filter
          (fun s => SkewTree.strictPrefixB s
            (projected c ⟨i,z⟩).1 = true)).card :=
      Finset.card_union_of_disjoint
        (final_projected_predecessor_filters_disjoint c f M i z)
    _ = SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        SkewTree.heightAt
          (f.vector.components i).toVariableWord.supportNodes z.1 := by
        rw [hOld,hNew]

/-- Every SELECTED newly projected vertex lies at intrinsic
rank strictly below the FINAL target height M, not merely
below the original ambient complete-support height. -/
theorem final_projected_height_lt_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 < M := by
  rw [final_projected_height_formula c f M i z hz]
  have hBudget :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).2
  unfold FitsTargetHeight at hBudget
  dsimp only at hBudget
  omega

/-- Every new root selected for the final support T'_M,
not just a particular tagged representative, has final
intrinsic rank below M. Injectivity ensures its tag is
unique, but mere image membership already supplies one. -/
theorem final_all_selected_projected_heights_lt_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b)
    (ht : t ∈ selectedProjectedRoots c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList t < M := by
  classical
  obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp ht
  rcases u with ⟨i,z⟩
  have hz := final_projected_height_lt_target c f M i z hu
  simpa only [heq] using hz

end DualTree.ForwardQFinalIntrinsicRank
