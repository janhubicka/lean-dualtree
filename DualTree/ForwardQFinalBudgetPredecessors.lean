import DualTree.ForwardQFinalHeightBudget
import DualTree.ForwardQFinalProjectionOrder
import DualTree.SupportHeightRanks

/-!
# Predecessor geometry for the exact rank-budgeted final support

The final Lemma 27 ambient support is the union of the retained
initial part of the COMPLETE ambient support T and the projected
post-Ramsey local roots whose local rank plus frontier T-rank
falls strictly below the target final height M.

For the subsequent intrinsic-height theorem the essential
predecessor facts are:

* a retained T vertex precedes P_i(z) exactly when it precedes
  the genuine frontier t_i; no retained vertex can occur between
  t_i and its projected descendant;
* proper T predecessors of each frontier are retained;
* the target-height budget is hereditary under strict local
  support prefixes, and the projected canonical map preserves
  those strict local prefixes.

These lemmas avoid any Hall matching into the old source
variables and do NOT substitute ambient T-rank for the still
unproved intrinsic rank in the newly constructed final support.

The main pending step is a disjoint predecessor-set decomposition
and a cardinality equation for heightAt(T'_M,P_i(z)).
-/

namespace DualTree.ForwardQFinalBudgetPredecessors

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- A retained old T vertex prefixes a projected new root iff
it already prefixes that root's minimal outside-cut frontier.
The reverse implication follows from the projection cone; the
forward one uses the fact that a retained vertex cannot lie
strictly below an outside-cut frontier. -/
theorem retained_prefix_projected_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c)
    (s : Node b)
    (hs : s ∈ retained c) :
    IsPrefix s (projected c u).1 ↔
      IsPrefix s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut u.1).1 := by
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1
  have htProj : IsPrefix t (projected c u).1 :=
    projected_cone c u
  constructor
  · intro hsp
    rcases le_total s.length t.length with hlen | hlen
    · exact CutFrontier.prefix_of_prefix_length_le
        hsp htProj hlen
    · have hts : IsPrefix t s :=
        CutFrontier.prefix_of_prefix_length_le
          htProj hsp hlen
      have hbefore : ForwardAux s c.cut :=
        (Finset.mem_filter.mp hs).2
      have hfrontBefore : ForwardAux t c.cut :=
        ForwardInclusiveFrontier.forwardAux_of_prefix
          hts hbefore
      exact False.elim
        ((ForwardOrderedProjections.frontierAt_spec
          c.T c.cut u.1).2.1 hfrontBefore)
  · intro hst
    exact isPrefix_trans hst htProj

/-- Every retained prefix of a projected node is PROPER,
because projected nodes are all strictly outside the inclusive
cut while the old support is inside. -/
theorem retained_strictPrefix_projected_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c)
    (s : Node b)
    (hs : s ∈ retained c) :
    IsStrictPrefix s (projected c u).1 ↔
      IsPrefix s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut u.1).1 := by
  constructor
  · intro h
    exact (retained_prefix_projected_iff c u s hs).1 h.1
  · intro h
    have hp : IsPrefix s (projected c u).1 :=
      (retained_prefix_projected_iff c u s hs).2 h
    refine ⟨hp, ?_⟩
    intro heq
    have hbefore : ForwardAux s c.cut :=
      (Finset.mem_filter.mp hs).2
    have hpBefore : ForwardAux (projected c u).1 c.cut := by
      simpa only [heq] using hbefore
    exact (projected_outside_cut c u) hpBefore

/-- Every strict T predecessor of a corrected outside-cut
frontier is retained. Conversely, every retained prefix of
that frontier must be strict because the frontier itself is
outside the inclusive cut. -/
theorem T_predecessor_frontier_iff_retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (s : Node b)
    (hs : s ∈ c.T) :
    IsStrictPrefix s
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 ↔
    s ∈ retained c ∧
      IsPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have hfront := ForwardOrderedProjections.frontierAt_spec
    c.T c.cut i
  constructor
  · intro hpre
    have hbefore : ForwardAux s c.cut :=
      hfront.2.2 s hs hpre
    refine ⟨?_,hpre.1⟩
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hs,hbefore⟩
  · rintro ⟨hret,hpre⟩
    refine ⟨hpre,?_⟩
    intro heq
    have hbefore : ForwardAux s c.cut :=
      (Finset.mem_filter.mp hret).2
    rw [heq] at hbefore
    exact hfront.2.1 hbefore

/-- The selected local variable roots are prefix-closed
RELATIVE TO THE LOCAL VARIABLE SUPPORT. In particular, no
earlier root along a chosen local branch can be removed by
the target M rank cutoff if the later root is retained. -/
theorem selectedLocalRoots_prefix_closed_in_coordinate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : w ∈ (f.vector.components i).support)
    (hwz : IsStrictPrefix w.1 z.1) :
    (⟨i,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M := by
  classical
  have hzBudget : FitsTargetHeight c f M ⟨i,z⟩ :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).2
  let S := (f.vector.components i).toVariableWord.supportNodes
  have hwSupport : w.1 ∈ S := by
    change w.1 ∈ ((f.vector.components i).support.map
      (fun t => t.1))
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hlt : SkewTree.heightAt S w.1 <
      SkewTree.heightAt S z.1 :=
    SupportHeightRanks.heightAt_lt_of_strictPrefix
      S hwSupport hwz
  have hwBudget : FitsTargetHeight c f M ⟨i,w⟩ := by
    change SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes w.1 <
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 at hlt
    unfold FitsTargetHeight at hzBudget ⊢
    dsimp only at hzBudget ⊢
    omega
  have hwTagged :
      (⟨i,w⟩ : LocalAddress c) ∈ taggedLocalRoots c f := by
    unfold taggedLocalRoots
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨w,List.mem_toFinset.mpr hw,rfl⟩
  exact (selectedLocalRoots_mem_iff c f M ⟨i,w⟩).2
    ⟨hwTagged,hwBudget⟩

/-- Strict prefixes of genuinely selected local root addresses
also give strict prefixes of their actual projected T vertices,
and the filtered root set retains these intermediate vertices. -/
theorem selected_projected_predecessor_of_local_prefix
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : w ∈ (f.vector.components i).support)
    (hwz : IsStrictPrefix w.1 z.1) :
    (⟨i,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M ∧
    IsStrictPrefix (projected c ⟨i,w⟩).1
      (projected c ⟨i,z⟩).1 := by
  have hwSelected :=
    selectedLocalRoots_prefix_closed_in_coordinate
      c f M i z w hz hw hwz
  refine ⟨hwSelected, ?_⟩
  have hp :
      IsPrefix (projected c ⟨i,w⟩).1
        (projected c ⟨i,z⟩).1 :=
    (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
      c i w z).2 hwz.1
  refine ⟨hp, ?_⟩
  intro heq
  have hw_eq_z : w = z :=
    projectLocal_injective c i (Subtype.ext heq)
  exact hwz.2 (congrArg Subtype.val hw_eq_z)

end DualTree.ForwardQFinalBudgetPredecessors
