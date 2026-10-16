import DualTree.ForwardQFinalRetainedRanks
import DualTree.ForwardQFinalProjectionOrder

/-!
# Classifying all NEW strict predecessors in the exact final support

For the final rank equation in Lemma 27 we have already counted
old retained predecessors of P_i(z), and proved the target-height
budget is hereditary on strict local variable-support prefixes.

This module proves the corresponding exact NEW predecessor
classification. A selected projected vertex strictly preceding
P_i(z) cannot lie in a different sorted outside-cut frontier:
the two frontier cones are disjoint. Within the same frontier
the canonical projection preserves and REFLECTS the strict
prefix order.

Provided z itself belongs to the selected target-height budget,
the new predecessor condition therefore simplifies to:
  w is a genuine variable root in the i-th local component
  AND w is a strict prefix of z,
without a separate rank-budget test on w. The hereditary
budget theorem guarantees its selection.

This is an exact logical characterization of the predecessor
set, not yet a cardinality equality or a complete-skew theorem.
-/

namespace DualTree.ForwardQFinalSelectedPredecessors

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalBudgetPredecessors

/-- Membership of a specific tagged local root is EXACTLY
membership in the genuine support of its coordinate word.
The Finset construction does not create any extra local tags. -/
theorem taggedLocalRoots_mk_iff
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (w : BoundedNode b (k - (m + 1))) :
    (⟨i,w⟩ : LocalAddress c) ∈ taggedLocalRoots c f ↔
      w ∈ (f.vector.components i).support := by
  classical
  constructor
  · intro h
    change (⟨i,w⟩ : LocalAddress c) ∈
      (Finset.univ : Finset (Index c)).biUnion (fun j =>
        (f.vector.components j).support.toFinset.image
          (fun z => (⟨j,z⟩ : LocalAddress c))) at h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hj
    cases heq
    exact List.mem_toFinset.mp hz
  · intro hw
    unfold taggedLocalRoots
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr
      ⟨w,List.mem_toFinset.mpr hw,rfl⟩

/-- A strict prefix relation between projected nodes forces
equality of frontier indices. It then reflects to a strict
prefix relation of their original local address words. -/
theorem projected_strict_predecessor_same_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (v : LocalAddress c)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hpre : IsStrictPrefix
      (projected c v).1 (projected c ⟨i,z⟩).1) :
    ∃ w : BoundedNode b (k - (m + 1)),
      v = ⟨i,w⟩ ∧ IsStrictPrefix w.1 z.1 := by
  rcases v with ⟨j,w⟩
  have hji : j = i := by
    by_contra hne
    exact (projected_incomparable_of_distinct_frontiers
      c ⟨j,w⟩ ⟨i,z⟩ hne).1 hpre.1
  subst j
  refine ⟨w,rfl,?_⟩
  have hlocal : IsPrefix w.1 z.1 :=
    (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
      c i w z).1 hpre.1
  refine ⟨hlocal,?_⟩
  intro hEq
  have hwz : w = z := Subtype.ext hEq
  subst w
  exact hpre.2 rfl

/-- Selected new projected strict predecessors of P_i(z)
are precisely projections of SELECTED local roots
strictly preceding z in that very same coordinate. -/
theorem selected_new_predecessor_iff
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (s : Node b) :
    (s ∈ selectedProjectedRoots c f M ∧
      IsStrictPrefix s (projected c ⟨i,z⟩).1) ↔
    ∃ w : BoundedNode b (k - (m + 1)),
      (⟨i,w⟩ : LocalAddress c) ∈ selectedLocalRoots c f M ∧
      IsStrictPrefix w.1 z.1 ∧
      s = (projected c ⟨i,w⟩).1 := by
  classical
  constructor
  · rintro ⟨hselected,hpre⟩
    obtain ⟨u, hu, hnode⟩ := Finset.mem_image.mp hselected
    have hproj : IsStrictPrefix
        (projected c u).1 (projected c ⟨i,z⟩).1 := by
      simpa only [hnode] using hpre
    obtain ⟨w, heq, hlocal⟩ :=
      projected_strict_predecessor_same_frontier c u i z hproj
    subst u
    exact ⟨w,hu,hlocal,hnode.symm⟩
  · rintro ⟨w,hw,hlocal,hs⟩
    refine ⟨?_,?_⟩
    · exact Finset.mem_image.mpr
        ⟨⟨i,w⟩,hw,hs.symm⟩
    · rw [hs]
      have hproj : IsPrefix
          (projected c ⟨i,w⟩).1
          (projected c ⟨i,z⟩).1 :=
        (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
          c i w z).2 hlocal.1
      refine ⟨hproj,?_⟩
      intro hEq
      have hwz : w = z :=
        projectLocal_injective c i (Subtype.ext hEq)
      exact hlocal.2 (congrArg Subtype.val hwz)

/-- Once z itself passes the target M budget, strict new
predecessors do NOT need a second filter: every earlier
local support root automatically passes the budget. -/
theorem selected_new_predecessor_iff_local_support
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (s : Node b) :
    (s ∈ selectedProjectedRoots c f M ∧
      IsStrictPrefix s (projected c ⟨i,z⟩).1) ↔
    ∃ w : BoundedNode b (k - (m + 1)),
      w ∈ (f.vector.components i).support ∧
      IsStrictPrefix w.1 z.1 ∧
      s = (projected c ⟨i,w⟩).1 := by
  constructor
  · intro h
    obtain ⟨w,hw,hpre,hs⟩ :=
      (selected_new_predecessor_iff c f M i z s).1 h
    have htag :
        (⟨i,w⟩ : LocalAddress c) ∈ taggedLocalRoots c f :=
      ((selectedLocalRoots_mem_iff c f M ⟨i,w⟩).1 hw).1
    exact ⟨w,(taggedLocalRoots_mk_iff c f i w).1 htag,
      hpre,hs⟩
  · rintro ⟨w,hw,hpre,hs⟩
    have hselected :
        (⟨i,w⟩ : LocalAddress c) ∈ selectedLocalRoots c f M :=
      selectedLocalRoots_prefix_closed_in_coordinate
        c f M i z w hz hw hpre
    exact (selected_new_predecessor_iff c f M i z s).2
      ⟨w,hselected,hpre,hs⟩

end DualTree.ForwardQFinalSelectedPredecessors
