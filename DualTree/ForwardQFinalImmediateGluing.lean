import DualTree.ForwardQFinalSelectedPredecessors
import DualTree.ForwardQFinalBudgetPredecessors

/-!
# Genuine immediate support edges survive projection into final T'_M

The exact rank-filtered final support contains retained initial
ambient T vertices and selected projected local roots P_i(z).
A local support-immediate edge z -> w in one coordinate,
with both endpoints retained by the target-height filter,
is still an immediate edge in the ENTIRE glued final support.

Indeed:
  * there can be no retained vertex strictly between
    P_i(z) and P_i(w), since P_i(z) lies beyond the cut;
  * a selected projected vertex strictly preceding P_i(w)
    must come from the SAME frontier i and a strict local
    support predecessor of w; if it strictly follows P_i(z)
    it violates local immediacy of z -> w.

This is stronger than abstract prefix preservation but does
not assert that projection maps ambient immediate children
to ambient immediate children. It also does not yet establish
the converse that every final support edge comes from local
or retained edges, nor the full-b branching/completeness.
-/

namespace DualTree.ForwardQFinalImmediateGluing

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalSelectedPredecessors

/-- A locally immediate successor whose two local roots
are selected is also a genuine IMMEDIATE SUCCESSOR in
the FULL final filtered support T'_M (not merely a prefix).
The parent is verified to belong to the actual final support. -/
theorem selected_local_immediate_is_final_immediate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : (⟨i,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hlocal : SkewTree.immediateSuccB
      (f.vector.components i).toVariableWord.supportNodes
      z.1 w.1 = true) :
    (projected c ⟨i,z⟩).1 ∈ (finalBudgetSupport c f M).toList ∧
    SkewTree.immediateSuccB (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1
      (projected c ⟨i,w⟩).1 = true := by
  classical
  let L := (f.vector.components i).toVariableWord.supportNodes
  let S := (finalBudgetSupport c f M).toList
  have hparent : (projected c ⟨i,z⟩).1 ∈ S := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_image.mpr
      ⟨⟨i,z⟩,hz,rfl⟩)
  have hchild : (projected c ⟨i,w⟩).1 ∈ S := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_image.mpr
      ⟨⟨i,w⟩,hw,rfl⟩)
  have hloc := (SkewBranchGeometry.immediateSuccB_iff L z.1 w.1).1
    hlocal
  have hp : IsStrictPrefix (projected c ⟨i,z⟩).1
      (projected c ⟨i,w⟩).1 := by
    have hpre := (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
      c i z w).2 hloc.2.1.1
    refine ⟨hpre,?_⟩
    intro heq
    have hzEqW : z = w :=
      projectLocal_injective c i (Subtype.ext heq)
    exact hloc.2.1.2 (congrArg Subtype.val hzEqW)
  refine ⟨hparent,?_⟩
  apply (SkewBranchGeometry.immediateSuccB_iff S
    (projected c ⟨i,z⟩).1 (projected c ⟨i,w⟩).1).2
  refine ⟨hchild,hp,?_⟩
  intro s hs hbetween
  have hmem : s ∈ finalBudgetSupport c f M :=
    Finset.mem_toList.mp hs
  rcases Finset.mem_union.mp hmem with hret | hnew
  · exact (projected_not_prefix_retained c ⟨i,z⟩ s hret)
      hbetween.1.1
  · obtain ⟨v,hv,hstrictW,hsEq⟩ :=
      (selected_new_predecessor_iff_local_support
        c f M i w hw s).1 ⟨hnew,hbetween.2⟩
    have hzvP : IsStrictPrefix
        (projected c ⟨i,z⟩).1
        (projected c ⟨i,v⟩).1 := by
      simpa only [hsEq] using hbetween.1
    have hzvPrefix : IsPrefix z.1 v.1 :=
      (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
        c i z v).1 hzvP.1
    have hzvNe : z.1 ≠ v.1 := by
      intro heq
      have hzEqV : z = v := Subtype.ext heq
      subst v
      exact hzvP.2 rfl
    have hvNode : v.1 ∈ L := by
      change v.1 ∈ (f.vector.components i).support.map
        (fun x => x.1)
      exact List.mem_map.mpr ⟨v,hv,rfl⟩
    exact hloc.2.2 v.1 hvNode
      ⟨⟨hzvPrefix,hzvNe⟩,hstrictW⟩

end DualTree.ForwardQFinalImmediateGluing
