import DualTree.ForwardQFinalRetainedChildConverse
import DualTree.ForwardInclusiveFrontier
import DualTree.MeetClosedDirectionConverse

/-!
# Uniqueness of outgoing directions from retained vertices of final T'

The corrected Lemma 27 support T'_M contains the retained
initial ambient T cut and projected coordinate roots.

For directional uniqueness, exhibiting a canonical selected
child is not enough: an arbitrary final immediate child in the
same ambient direction must be shown equal to that choice.

The verified retained-child converse gives two possibilities
for each final immediate child x of retained s:

* x itself is retained, and s -> x is a genuine immediate
  edge in the original complete ambient support T;
* x = P_i(localRoot_i), and s -> frontier_i is the
  genuine immediate T edge that x replaces.

The first direction of the final child also determines
the first direction of this ambient T edge: the frontier
lies between s and the projected root and its ambient
length is greater than |s|.

The original complete support T is meet-closed, hence has
at most one immediate successor in each ambient direction.
Therefore the two ambient predecessors for competing final
children coincide. A retained endpoint cannot equal an
outside-cut frontier. If both endpoints are projected,
injectivity of sorted frontier coordinates forces the same
localRoot image. Thus x=y.

No meet closure or complete-skewness is assumed for T'_M.
The remaining global structural checks are the skew-order
and branching height conditions and the actual final word f'.
-/

namespace DualTree.ForwardQFinalRetainedDirectionUniqueness

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalLocalRoots

/-- Every immediate final child in a fixed direction from
a retained parent corresponds to one actual immediate
AMBIENT T child in that SAME direction. The final child
is either literally the retained T child or the selected
root P_i(localRoot_i) replacing an outside-cut frontier. -/
theorem retained_final_child_has_ambient_witness
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s : Node b)
    (hs : s ∈ retained c)
    (dir : Fin b)
    (x : Node b)
    (hx : x ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f M).toList s dir) :
    ∃ t : Node b,
      SkewTree.immediateSuccB c.T s t = true ∧
      IsPrefix (s ++ [dir]) t ∧
      ((x = t ∧ t ∈ retained c) ∨
        ∃ i : Index c,
          t = (ForwardOrderedProjections.frontierAt
            c.T c.cut i).1 ∧
          x = (projected c ⟨i,localRoot c f i⟩).1) := by
  classical
  have hdata :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      (finalBudgetSupport c f M).toList s x dir).1 hx
  obtain ⟨hstep,hcone⟩ := hdata
  have hxMem : x ∈ finalBudgetSupport c f M :=
    Finset.mem_toList.mp
      ((SkewBranchGeometry.immediateSuccB_iff
        (finalBudgetSupport c f M).toList s x).1 hstep).1
  rcases Finset.mem_union.mp hxMem with hret | hnew
  · have hambient :
        SkewTree.immediateSuccB c.T s x = true :=
      ForwardQFinalRetainedChildConverse.retained_final_immediate_is_ambient_immediate
        c f M s x hs hret hstep
    exact ⟨x,hambient,hcone,Or.inl ⟨rfl,hret⟩⟩
  · obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hnew
    rcases u with ⟨i,z⟩
    have hstepP :
        SkewTree.immediateSuccB
          (finalBudgetSupport c f M).toList
          s (projected c ⟨i,z⟩).1 = true := by
      simpa only [heq] using hstep
    obtain ⟨hambient,hroot⟩ :=
      ForwardQFinalRetainedChildConverse.retained_final_projected_child_is_frontier_localRoot
        c f M s hs i z hu hstepP
    let t := (ForwardOrderedProjections.frontierAt
      c.T c.cut i).1
    have hstrict :
        IsStrictPrefix s t :=
      ((SkewBranchGeometry.immediateSuccB_iff c.T s t).1
        hambient).2.1
    have hfrontCone : IsPrefix t (projected c ⟨i,z⟩).1 :=
      projected_cone c ⟨i,z⟩
    have hdirP :
        IsPrefix (s ++ [dir]) (projected c ⟨i,z⟩).1 := by
      simpa only [heq] using hcone
    have hlen : (s ++ [dir]).length ≤ t.length := by
      have hlt :=
        MeetClosedFromBranching.length_lt_of_strictPrefix hstrict
      simp only [List.length_append,List.length_singleton]
      omega
    have hdirT : IsPrefix (s ++ [dir]) t :=
      CutFrontier.prefix_of_prefix_length_le
        hdirP hfrontCone hlen
    have hxRoot :
        x = (projected c ⟨i,localRoot c f i⟩).1 := by
      calc
        x = (projected c ⟨i,z⟩).1 := heq.symm
        _ = (projected c ⟨i,localRoot c f i⟩).1 := by rw [hroot]
    exact ⟨t,hambient,hdirT,Or.inr ⟨i,rfl,hxRoot⟩⟩

/-- At every retained final-support vertex, no two distinct
immediate successors can occupy the SAME ambient direction.
This holds without requiring that the vertex actually
branches or that the joined final support is meet-closed. -/
theorem retained_atMostOneDirection
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s : Node b)
    (hs : s ∈ retained c)
    (dir : Fin b)
    (x y : Node b)
    (hx : x ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f M).toList s dir)
    (hy : y ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f M).toList s dir) :
    x = y := by
  classical
  obtain ⟨tx,htx,hdirx,hrepX⟩ :=
    retained_final_child_has_ambient_witness
      c f M s hs dir x hx
  obtain ⟨ty,hty,hdiry,hrepY⟩ :=
    retained_final_child_has_ambient_witness
      c f M s hs dir y hy
  have hsT : s ∈ c.T := retained_subset_T c s hs
  have hmeet : MeetGeometry.MeetClosed c.T :=
    ForwardInclusiveFrontier.meetClosed_complete_forward
      c.T c.hcomplete c.hnon
  have hUnique : MeetClosedFromBranching.AtMostOneDirection c.T :=
    MeetClosedDirectionConverse.atMostOneDirection_of_meetClosed
      c.T hmeet
  have hxAmbient :
      tx ∈ SkewTree.branchWitnesses c.T s dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff c.T s tx dir).2
      ⟨htx,hdirx⟩
  have hyAmbient :
      ty ∈ SkewTree.branchWitnesses c.T s dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff c.T s ty dir).2
      ⟨hty,hdiry⟩
  have hEqual : tx = ty :=
    hUnique s hsT dir tx ty hxAmbient hyAmbient
  rcases hrepX with ⟨hxEq,hxRet⟩ | ⟨i,hfrontX,himageX⟩
  · rcases hrepY with ⟨hyEq,hyRet⟩ | ⟨j,hfrontY,himageY⟩
    · exact hxEq.trans (hEqual.trans hyEq.symm)
    · have hbefore : ForwardAux tx c.cut :=
        (Finset.mem_filter.mp hxRet).2
      have houtside :
          ¬ ForwardAux
            (ForwardOrderedProjections.frontierAt
              c.T c.cut j).1 c.cut :=
        (ForwardOrderedProjections.frontierAt_spec c.T c.cut j).2.1
      have hbad : ForwardAux
          (ForwardOrderedProjections.frontierAt
            c.T c.cut j).1 c.cut := by
        rw [← hfrontY, ← hEqual]
        exact hbefore
      exact False.elim (houtside hbad)
  · rcases hrepY with ⟨hyEq,hyRet⟩ | ⟨j,hfrontY,himageY⟩
    · have hbefore : ForwardAux ty c.cut :=
        (Finset.mem_filter.mp hyRet).2
      have houtside :
          ¬ ForwardAux
            (ForwardOrderedProjections.frontierAt
              c.T c.cut i).1 c.cut :=
        (ForwardOrderedProjections.frontierAt_spec c.T c.cut i).2.1
      have hbad : ForwardAux
          (ForwardOrderedProjections.frontierAt
            c.T c.cut i).1 c.cut := by
        rw [← hfrontX, hEqual]
        exact hbefore
      exact False.elim (houtside hbad)
    · have hfrontEq :
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
          (ForwardOrderedProjections.frontierAt c.T c.cut j).1 := by
        calc
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
              tx := hfrontX.symm
          _ = ty := hEqual
          _ = (ForwardOrderedProjections.frontierAt
            c.T c.cut j).1 := hfrontY
      have hij : i = j :=
        ForwardOrderedProjections.frontierAt_injective c.T c.cut
          (Subtype.ext hfrontEq)
      calc
        x = (projected c ⟨i,localRoot c f i⟩).1 := himageX
        _ = (projected c ⟨j,localRoot c f j⟩).1 := by rw [hij]
        _ = y := himageY.symm

end DualTree.ForwardQFinalRetainedDirectionUniqueness
