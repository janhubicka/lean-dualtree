import DualTree.ForwardQFinalRetainedFrontierGluing
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalLocalRoots
import DualTree.ForwardSortedFrontiers

/-!
# Eliminating the remaining index hypothesis in retained/new gluing

Every ambient T immediate edge s->t crossing the corrected
inclusive cut from a retained vertex s lands at a genuine
minimal outside-cut frontier t (previously verified).
This frontier must be one of the actually sorted
coordinate roots t_i of the mixed product:
the membership equivalence for the sorted finite
frontier list yields a concrete Fin index i.

Now take the FINAL target height M=m+q. If the
retained parent s is early enough to need a successor,
namely height_T(s)+1 < m+q, then the local root z_i
of its post-Ramsey q-complete component is SELECTED.

If height_T(t_i)=m, this follows for every local root.
If height_T(t_i)=m+1, immediacy gives
height_T(t_i)=height_T(s)+1, so the early-parent
hypothesis forces q>=2; the zero-rank local root
then passes the upper frontier's one-shorter cutoff.

Finally the already verified one-rank-gap gluing lemma
replaces the outside T endpoint t by the selected
projection P_i(z_i), as an actual immediate T'_M
support successor in the SAME outgoing direction.

These are the complete RETAINED-TO-NEW crossing
branch-existence lemmas. Full branching at retained
vertices still requires the case split over the
T-successor staying retained or crossing the cut,
and complete skewness still requires uniqueness and
global length/order conditions.
-/

namespace DualTree.ForwardQFinalRetainedCrossing

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalTwoFrontierBudget
open ForwardQFinalLocalRoots

/-- Every genuine immediate T-edge crossing from a
retained vertex to an outside-cut vertex identifies
an actual coordinate of the FINITE SORTED frontiers.
The frontier is literally t, not an arbitrarily
chosen ancestor or a reordered index. -/
theorem crossing_immediate_has_sorted_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true)
    (hout : ¬ ForwardAux t c.cut) :
    ∃ i : Index c,
      (ForwardOrderedProjections.frontierAt
        c.T c.cut i).1 = t := by
  have hf :=
    ForwardQFinalRetainedEdges.outside_immediate_T_edge_is_frontier
      c s t hs hstep hout
  have hmem :
      t ∈ ForwardSortedFrontiers.frontiers c.T c.cut :=
    (ForwardSortedFrontiers.mem_frontiers_iff
      c.T c.cut t).2 hf
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
  refine ⟨i,?_⟩
  change (ForwardSortedFrontiers.frontiers c.T c.cut).get i = t
  exact hi

/-- An immediate crossing T-edge from a retained parent
that still needs a next level at target M=m+q always
selects the actual root of the corresponding local
coordinate support. This resolves the m/m+1
frontier rank dichotomy with NO additional capacity
or Hall hypothesis. -/
theorem crossing_immediate_selects_local_root
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s t : Node b)
    (hs : s ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true)
    (hout : ¬ ForwardAux t c.cut)
    (hroom : SkewTree.heightAt c.T s + 1 < m+q) :
    ∃ i : Index c,
      (ForwardOrderedProjections.frontierAt
        c.T c.cut i).1 = t ∧
      (⟨i,localRoot c f i⟩ : LocalAddress c) ∈
        selectedLocalRoots c f (m+q) := by
  obtain ⟨i,hit⟩ :=
    crossing_immediate_has_sorted_frontier
      c s t hs hstep hout
  have hstepRank : SkewTree.heightAt c.T t =
      SkewTree.heightAt c.T s + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      c.T s t (ForwardQFinalRetainedRanks.ambientT_nodup c)
      (retained_subset_T c s hs) hstep
  refine ⟨i,hit,?_⟩
  rcases frontier_rank_cut_or_succ c i with hSame | hPlus
  · exact selected_of_rank_m_frontier c f i
      (localRoot c f i) hSame
      (localRoot_mem c f i)
  · have hPlusT : SkewTree.heightAt c.T t = m+1 := by
      rw [← hit]
      exact hPlus
    have hq : 2 ≤ q := by
      rw [hstepRank] at hPlusT
      omega
    apply (selected_rank_succ_iff c f i
      (localRoot c f i) hPlus).2
    refine ⟨localRoot_mem c f i,?_⟩
    rw [localRoot_height_zero c f i]
    omega

/-- The selected projected local root REPLACES every
crossing immediate T-edge from an early retained parent.
It is an actual immediate edge of the WHOLE final
support T'_(m+q) and preserves the specified ambient
first direction, with no pre-chosen frontier index. -/
theorem crossing_immediate_has_replacement_in_direction
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s t : Node b)
    (hs : s ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true)
    (hout : ¬ ForwardAux t c.cut)
    (hroom : SkewTree.heightAt c.T s + 1 < m+q)
    (dir : Fin b)
    (hdir : IsPrefix (s ++ [dir]) t) :
    ∃ i : Index c,
      SkewTree.immediateSuccB
        (finalBudgetSupport c f (m+q)).toList s
        (projected c ⟨i,localRoot c f i⟩).1 = true ∧
      IsPrefix (s ++ [dir])
        (projected c ⟨i,localRoot c f i⟩).1 := by
  obtain ⟨i,hit,hselected⟩ :=
    crossing_immediate_selects_local_root
      c f s t hs hstep hout hroom
  have hstepI :
      SkewTree.immediateSuccB c.T s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true := by
    rw [hit]
    exact hstep
  have hdirI :
      IsPrefix (s ++ [dir])
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 := by
    rw [hit]
    exact hdir
  exact ⟨i,
    ForwardQFinalRetainedFrontierGluing.retained_frontier_localRoot_immediate_in_direction
      c f (m+q) s hs i hstepI hselected dir hdirI⟩

end DualTree.ForwardQFinalRetainedCrossing
