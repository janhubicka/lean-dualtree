import DualTree.ForwardQFinalRetainedChildConverse
import DualTree.ForwardQFinalProjectedFullDirections
import DualTree.ForwardQFinalSelectedPredecessors
import DualTree.ForwardQFinalIntrinsicRank

/-!
# Converse classification of immediate children of PROJECTED final roots

The checked Lemma 27 final construction produces immediate edges
between selected projected local support roots. For directional
uniqueness we must show that every possible immediate final
child of a projected parent P_i(z) is of this form.

A final immediate child t cannot be retained because every
selected projection lies beyond the inclusive cut. By
prefix-incomparability of different frontier cones, t must
be the projection P_i(w) of another selected local support
root in the SAME frontier. Reflection of prefixes shows
z is a strict local support prefix of w.

Since the final edge is immediate, the intrinsic rank of
P_i(w) is exactly one above P_i(z). The already checked
final rank identities cancel their common ambient frontier
contribution, yielding

    height_ws(f_i)(w) = height_ws(f_i)(z) + 1.

Thus z -> w is actually a LOCAL immediate support edge
by the generic strict-prefix/consecutive-rank criterion.

No meet-closure, Hall matching or full-skewness premise
is assumed. Direction-labelled uniqueness still needs
the check that two different local immediate successors
cannot project into the same ambient direction.
-/

namespace DualTree.ForwardQFinalProjectedChildConverse

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- Any immediate full T'_M child of a selected projected
parent P_i(z) is a selected projection P_i(w) from the
SAME frontier, with z a strict LOCAL prefix of w. Neither
retained vertices nor other frontier coordinates can
provide competing immediate children. -/
theorem selected_final_immediate_child_same_frontier
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (t : Node b)
    (hstep : SkewTree.immediateSuccB
      (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 t = true) :
    ∃ w : BoundedNode b (k-(m+1)),
      (⟨i,w⟩ : LocalAddress c) ∈ selectedLocalRoots c f M ∧
      IsStrictPrefix z.1 w.1 ∧
      t = (projected c ⟨i,w⟩).1 := by
  classical
  let S := (finalBudgetSupport c f M).toList
  obtain ⟨ht,hstrict,_⟩ :=
    (SkewBranchGeometry.immediateSuccB_iff S
      (projected c ⟨i,z⟩).1 t).1 hstep
  have htFin : t ∈ finalBudgetSupport c f M :=
    Finset.mem_toList.mp ht
  rcases Finset.mem_union.mp htFin with hret | hnew
  · exact False.elim
      ((projected_not_prefix_retained c ⟨i,z⟩ t hret)
        hstrict.1)
  · obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hnew
    rcases u with ⟨j,w⟩
    have hproj : IsStrictPrefix
        (projected c ⟨i,z⟩).1
        (projected c ⟨j,w⟩).1 := by
      simpa only [heq] using hstrict
    have hji : j = i := by
      by_contra hne
      exact
        (projected_incomparable_of_distinct_frontiers
          c ⟨i,z⟩ ⟨j,w⟩ hne.symm).1 hproj.1
    subst j
    have hlocalPre : IsPrefix z.1 w.1 :=
      (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
        c i z w).1 hproj.1
    have hlocalNe : z.1 ≠ w.1 := by
      intro hval
      have heqZW : z = w := Subtype.ext hval
      subst w
      exact hproj.2 rfl
    exact ⟨w,hu,⟨hlocalPre,hlocalNe⟩,heq.symm⟩

/-- The corresponding local edge z -> w is actually an
IMMEDIATE local support edge. A final immediate edge
has a one-rank gap; the exact final projected-rank
formula cancels the common ambient frontier term.
No intermediate local support root can fit between
two consecutive intrinsic local support levels. -/
theorem selected_final_immediate_child_is_local_immediate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (t : Node b)
    (hstep : SkewTree.immediateSuccB
      (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 t = true) :
    ∃ w : BoundedNode b (k-(m+1)),
      (⟨i,w⟩ : LocalAddress c) ∈ selectedLocalRoots c f M ∧
      SkewTree.immediateSuccB
        (f.vector.components i).toVariableWord.supportNodes
        z.1 w.1 = true ∧
      t = (projected c ⟨i,w⟩).1 := by
  classical
  obtain ⟨w,hw,hlocalPre,heq⟩ :=
    selected_final_immediate_child_same_frontier
      c f M i z hz t hstep
  let S := (finalBudgetSupport c f M).toList
  let L := (f.vector.components i).toVariableWord.supportNodes
  have hzTag :
      (⟨i,z⟩ : LocalAddress c) ∈ taggedLocalRoots c f :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).1
  have hwTag :
      (⟨i,w⟩ : LocalAddress c) ∈ taggedLocalRoots c f :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,w⟩).1 hw).1
  have hzSupp : z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 hzTag
  have hwSupp : w ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i w).1 hwTag
  have hzL : z.1 ∈ L := by
    change z.1 ∈ (f.vector.components i).support.map
      (fun u => u.1)
    exact List.mem_map.mpr ⟨z,hzSupp,rfl⟩
  have hwL : w.1 ∈ L := by
    change w.1 ∈ (f.vector.components i).support.map
      (fun u => u.1)
    exact List.mem_map.mpr ⟨w,hwSupp,rfl⟩
  have hzFinal : (projected c ⟨i,z⟩).1 ∈ S := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_union.mpr
    exact Or.inr
      (Finset.mem_image.mpr ⟨⟨i,z⟩,hz,rfl⟩)
  have hgapFinal :
      SkewTree.heightAt S t =
      SkewTree.heightAt S (projected c ⟨i,z⟩).1 + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      S (projected c ⟨i,z⟩).1 t
      (Finset.nodup_toList (finalBudgetSupport c f M))
      hzFinal hstep
  have hgapProjected :
      SkewTree.heightAt S (projected c ⟨i,w⟩).1 =
      SkewTree.heightAt S (projected c ⟨i,z⟩).1 + 1 := by
    simpa only [heq] using hgapFinal
  have hrankZ :=
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i z hz
  have hrankW :=
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i w hw
  have hgapLocal :
      SkewTree.heightAt L w.1 =
        SkewTree.heightAt L z.1 + 1 := by
    change SkewTree.heightAt
      (finalBudgetSupport c f M).toList (projected c ⟨i,w⟩).1 =
      SkewTree.heightAt
        (finalBudgetSupport c f M).toList (projected c ⟨i,z⟩).1 + 1
      at hgapProjected
    rw [hrankW, hrankZ] at hgapProjected
    change SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes w.1 =
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 + 1
    omega
  have hlocal :
      SkewTree.immediateSuccB L z.1 w.1 = true :=
    ForwardQFinalProjectedFullDirections.immediate_of_rank_succ
      L z.1 w.1 hzL hwL hlocalPre hgapLocal
  exact ⟨w,hw,hlocal,heq⟩

end DualTree.ForwardQFinalProjectedChildConverse
