import DualTree.ForwardQFinalLocalRoots
import DualTree.CompleteInteriorBranching
import DualTree.ImmediateSupportHeight

/-!
# Directional branching in the actual local post-Ramsey supports

For each q-complete mixed coordinate support, a vertex with
local intrinsic rank+1<q is a nonleaf. The complete-skew
axioms force a unique immediate LOCAL SUPPORT successor in
every ambient direction. CanonicalSupportWalk.next realizes
this successor, and its local intrinsic rank increases by one.

At a rank-m outside-cut frontier, the entire local support
survives the final target M=m+q filter. At a rank-(m+1)
frontier, successors survive whenever the parent has
local rank+2<q, precisely the one-level-shorter budget.

These are local support results; proving that the projected
successors are also the genuine immediate successors of
the FULL assembled T'_M requires additional gluing.
-/

namespace DualTree.ForwardQFinalLocalBranching

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalTwoFrontierBudget

/-- A local support root below the final intrinsic level
has at least one immediate support successor. -/
theorem local_nonleaf_of_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q) :
    (SkewTree.immediateSuccs
      (f.vector.components i).toVariableWord.supportNodes z.1).length ≠ 0 := by
  have hzNode :
      z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i).support.map (fun w => w.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  exact CompleteInteriorBranching.nonleaf_of_height_lt
    SkewTree.forwardAuxB
    (f.vector.components i).toVariableWord.supportNodes
    (local_component_complete c f i) z.1 hzNode hlevel

/-- Any local vertex below the last level gives a
nonsingleton variable support; the singleton case can
only arise at the terminal local level. -/
theorem local_nonsingleton_of_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q) :
    (f.vector.components i).toVariableWord.supportNodes.length ≠ 1 := by
  let T := (f.vector.components i).toVariableWord.supportNodes
  have hzNode : z.1 ∈ T := by
    change z.1 ∈ (f.vector.components i).support.map (fun w => w.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hnonleaf : (SkewTree.immediateSuccs T z.1).length ≠ 0 :=
    local_nonleaf_of_height c f i z hz hlevel
  cases hlist : SkewTree.immediateSuccs T z.1 with
  | nil =>
      exact False.elim (hnonleaf (by simp [hlist]))
  | cons u us =>
      have hu : u ∈ SkewTree.immediateSuccs T z.1 := by
        simp [hlist]
      have huFilter : u ∈ T.filter
          (fun t => SkewTree.immediateSuccB T z.1 t) := hu
      have huMem : u ∈ T := (List.mem_filter.mp huFilter).1
      have huImm : SkewTree.immediateSuccB T z.1 u = true :=
        (List.mem_filter.mp huFilter).2
      have hne : z.1 ≠ u :=
        ((SkewBranchGeometry.immediateSuccB_iff T z.1 u).1
          huImm).2.1.2
      exact SupportReachability.nonsingleton_of_distinct_members
        T hzNode huMem hne

/-- A q-complete local support has a unique immediate
support successor in EVERY ambient direction below its
last intrinsic level. -/
theorem local_full_directions_of_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hlevel : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q)
    (dir : Fin b) :
    SkewTree.uniqueBranchB
      (f.vector.components i).toVariableWord.supportNodes
      z.1 dir = true := by
  have hzNode :
      z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i).support.map (fun w => w.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hnonleaf := local_nonleaf_of_height c f i z hz hlevel
  apply CompleteInteriorBranching.fullDirections_of_complete_nonleaf_total
    SkewTree.forwardAuxB
    (f.vector.components i).toVariableWord.supportNodes
    (local_component_complete c f i)
    (local_nonsingleton_of_height c f i z hz hlevel)
    ?_ z.1 hzNode hnonleaf dir
  intro s t hne
  rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
  · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
  · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)

/-- The next local directional support vertex is again a
genuine bounded variable root, in the requested cone,
with intrinsic support rank increased by exactly one.
No immediate AMBIENT child assumption is made. -/
theorem local_directional_next_root
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
      IsPrefix (z.1 ++ [dir]) w.1 ∧
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes w.1 =
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 + 1 := by
  let T := (f.vector.components i).toVariableWord.supportNodes
  let u := CanonicalSupportWalk.next T z.1 dir
  have hzNode : z.1 ∈ T := by
    change z.1 ∈ (f.vector.components i).support.map (fun w => w.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have huniq : SkewTree.uniqueBranchB T z.1 dir = true :=
    local_full_directions_of_height c f i z hz hlevel dir
  have hnext := CanonicalSupportWalk.next_unique T z.1 dir huniq
  have hu : u ∈ T := CanonicalSupportWalk.next_mem T z.1 dir huniq
  have hn : T.Nodup :=
    VariableWord.supportNodes_nodup
      (f.vector.components i).toVariableWord
  have hrank : SkewTree.heightAt T u =
      SkewTree.heightAt T z.1 + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      T z.1 u hn hzNode hnext.1
  change u ∈ (f.vector.components i).support.map
    (fun w => w.1) at hu
  obtain ⟨w,hw,heq⟩ := List.mem_map.mp hu
  refine ⟨w,hw,?_,?_⟩
  · simpa only [heq] using hnext.2
  · simpa only [heq] using hrank

/-- Rank-m frontiers retain a genuine local successor
in every direction when the local parent is a nonleaf. -/
theorem selected_next_rank_m
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
      IsPrefix (z.1 ++ [dir]) w.1 := by
  obtain ⟨w,hw,hdir,_⟩ :=
    local_directional_next_root c f i z hz hlevel dir
  exact ⟨w,selected_of_rank_m_frontier c f i w hfront hw,hdir⟩

/-- At a rank-(m+1) frontier, the selected successor remains
available provided the local parent has TWO ranks of room
below q: the upper frontier's budget is one level shorter. -/
theorem selected_next_rank_succ
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
      IsPrefix (z.1 ++ [dir]) w.1 := by
  have hnonleaf : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q := by
    omega
  obtain ⟨w,hw,hdir,hrank⟩ :=
    local_directional_next_root c f i z hz hnonleaf dir
  have hbudget : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes w.1 + 1 < q := by
    rw [hrank]
    omega
  exact ⟨w,(selected_rank_succ_iff c f i w hfront).2
    ⟨hw,hbudget⟩,hdir⟩

end DualTree.ForwardQFinalLocalBranching
