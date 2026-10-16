import DualTree.ForwardQFinalLocalBranching
import DualTree.ForwardQFinalImmediateGluing
import DualTree.ForwardQFinalProjectionDirection
import DualTree.SupportHeightRanks

/-!
# Direction-labelled immediate successors of NEW roots in the glued T'_M

The original local word f_i is q-complete and has one immediate
support successor in every ambient direction below its final
local level. The exact target-M cutoff removes a top layer
above frontiers of T-rank m+1.

A selected local edge whose child has intrinsic local rank
one above its parent is immediate already INSIDE the local
support: any strict intermediate would have an intrinsic
rank strictly between two consecutive natural numbers.

The separately checked final-support gluing theorem shows
these selected local immediate edges remain immediate
in the entire final T'_M, even in the presence of other
frontier cones and retained old vertices.

The separately checked projected child-cone theorem
preserves the requested FIRST outgoing ambient direction,
not just the unordered prefix structure.

At rank-m frontiers this yields an immediate successor in
each direction at any local level r with r+1<q.
At rank-(m+1) frontiers the condition is r+2<q,
matching the paper's strict final-height budget.

These are positive full-direction existence statements
for selected NEW roots. Retained/new branching and
all global complete-skew axioms remain open.
-/

namespace DualTree.ForwardQFinalProjectedFullDirections

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalTwoFrontierBudget
open ForwardQFinalLocalBranching

/-- Strict support prefixes with consecutive intrinsic
ranks are already IMMEDIATE support edges. No skew,
meet-closure or duplicate-free hypothesis is needed. -/
theorem immediate_of_rank_succ
    {b : Nat}
    (S : List (Node b))
    (s t : Node b)
    (hs : s ∈ S)
    (ht : t ∈ S)
    (hpre : IsStrictPrefix s t)
    (hrank : SkewTree.heightAt S t =
      SkewTree.heightAt S s + 1) :
    SkewTree.immediateSuccB S s t = true := by
  apply (SkewBranchGeometry.immediateSuccB_iff S s t).2
  refine ⟨ht,hpre,?_⟩
  intro u hu hbetween
  have hlow :=
    SupportHeightRanks.heightAt_lt_of_strictPrefix
      S hs hbetween.1
  have hhigh :=
    SupportHeightRanks.heightAt_lt_of_strictPrefix
      S hu hbetween.2
  omega

/-- The actual local q-complete directional step is an
immediate support edge, not merely a node one level higher.
The requested direction is witnessed as a real cone prefix. -/
theorem local_directional_immediate_witness
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q)
    (dir : Fin b) :
    ∃ w : BoundedNode b (k-(m+1)),
      w ∈ (f.vector.components i).support ∧
      SkewTree.immediateSuccB
        (f.vector.components i).toVariableWord.supportNodes
        z.1 w.1 = true ∧
      IsPrefix (z.1 ++ [dir]) w.1 ∧
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes w.1 =
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 + 1 := by
  obtain ⟨w,hw,hdir,hrank⟩ :=
    local_directional_next_root c f i z hz hlevel dir
  let L := (f.vector.components i).toVariableWord.supportNodes
  have hzNode : z.1 ∈ L := by
    change z.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hwNode : w.1 ∈ L := by
    change w.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hprefix : IsPrefix z.1 w.1 :=
    isPrefix_trans ⟨[dir],rfl⟩ hdir
  have hlen : z.1.length < w.1.length := by
    have h := prefix_length_le hdir
    simp only [List.length_append,List.length_singleton] at h
    omega
  have hstrict : IsStrictPrefix z.1 w.1 :=
    ⟨hprefix,by
      intro hEq
      rw [hEq] at hlen
      omega⟩
  have hlocal :
      SkewTree.immediateSuccB L z.1 w.1 = true :=
    immediate_of_rank_succ L z.1 w.1
      hzNode hwNode hstrict hrank
  exact ⟨w,hw,hlocal,hdir,hrank⟩

/-- At a T-rank-m frontier, every local root below the
last local level has a genuine immediate successor in
each specified ambient direction in the FULL glued T'_M.
Both endpoints are selected and the ambient direction is
the original local direction, even if the edge is stretched. -/
theorem final_new_full_direction_rank_m
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q)
    (dir : Fin b) :
    ∃ w : BoundedNode b (k-(m+1)),
      (⟨i,w⟩ : LocalAddress c) ∈
        selectedLocalRoots c f (m+q) ∧
      SkewTree.immediateSuccB
        (finalBudgetSupport c f (m+q)).toList
        (projected c ⟨i,z⟩).1
        (projected c ⟨i,w⟩).1 = true ∧
      IsPrefix ((projected c ⟨i,z⟩).1 ++ [dir])
        (projected c ⟨i,w⟩).1 := by
  obtain ⟨w,hw,hlocal,hdir,_⟩ :=
    local_directional_immediate_witness
      c f i z hz hlevel dir
  have hzSelected :=
    selected_of_rank_m_frontier c f i z hfront hz
  have hwSelected :=
    selected_of_rank_m_frontier c f i w hfront hw
  have hfinal :=
    (ForwardQFinalImmediateGluing.selected_local_immediate_is_final_immediate
      c f (m+q) i z w hzSelected hwSelected hlocal).2
  have hprojected :=
    ForwardQFinalProjectionDirection.projected_childCone_mono
      c i z w dir hdir
  exact ⟨w,hwSelected,hfinal,hprojected⟩

/-- At an upper rank-(m+1) frontier, the final support is
one local level shorter. When local rank r satisfies
r+2<q, all requested immediate successors still belong
to the filtered T'_M and occupy their literal directions. -/
theorem final_new_full_direction_rank_succ
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m+1)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 2 < q)
    (dir : Fin b) :
    ∃ w : BoundedNode b (k-(m+1)),
      (⟨i,w⟩ : LocalAddress c) ∈
        selectedLocalRoots c f (m+q) ∧
      SkewTree.immediateSuccB
        (finalBudgetSupport c f (m+q)).toList
        (projected c ⟨i,z⟩).1
        (projected c ⟨i,w⟩).1 = true ∧
      IsPrefix ((projected c ⟨i,z⟩).1 ++ [dir])
        (projected c ⟨i,w⟩).1 := by
  have hnonleaf : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q := by
    omega
  obtain ⟨w,hw,hlocal,hdir,hrank⟩ :=
    local_directional_immediate_witness
      c f i z hz hnonleaf dir
  have hzCut : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q := by
    omega
  have hwCut : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes w.1 + 1 < q := by
    rw [hrank]
    omega
  have hzSelected : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f (m+q) :=
    (selected_rank_succ_iff c f i z hfront).2 ⟨hz,hzCut⟩
  have hwSelected : (⟨i,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f (m+q) :=
    (selected_rank_succ_iff c f i w hfront).2 ⟨hw,hwCut⟩
  have hfinal :=
    (ForwardQFinalImmediateGluing.selected_local_immediate_is_final_immediate
      c f (m+q) i z w hzSelected hwSelected hlocal).2
  have hprojected :=
    ForwardQFinalProjectionDirection.projected_childCone_mono
      c i z w dir hdir
  exact ⟨w,hwSelected,hfinal,hprojected⟩

end DualTree.ForwardQFinalProjectedFullDirections
