import DualTree.ForwardQFinalMixedCapacity

/-!
# Removing the last numerical premise from retained final branching

An actual Frame c has a cut vertex of ambient intrinsic rank m
with m+1<k. If the ambient alphabet b admits a direction dir
(i.e. dir : Fin b), k-completeness supplies a unique immediate
T successor of the cut in that direction. This successor has
T-rank m+1 and lies strictly BEYOND the inclusive forward cut.

The crossing-edge frontier theorem therefore yields a real
coordinate i of the actual finite sorted frontier family.
The genuine q-complete local variable word in coordinate i,
living on bounded tails of height k-(m+1), then forces
m+q<=k, as established in ForwardQFinalMixedCapacity.

Consequently the capacity condition needed to construct
retained final-support successors is derived from the
EXISTENCE of the requested direction; it is not a
new hypothesis in the final theorem. The b=0 case
is vacuous because there are no requested directions.

For every retained vertex of actual final rank r with
r+1<m+q, and for every dir : Fin b, there is an
immediate successor in that same dir in the ENTIRE
assembled T'_(m+q). No selection of a frontier index
or extra numerical premise remains.

This establishes directional EXISTENCE. The at-most-one
witness condition, global skew order and final word f'
are still separate obligations.
-/

namespace DualTree.ForwardQFinalRetainedUnconditional

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- Every actual requested direction at the distinguished cut
produces a genuine sorted outside-cut frontier. In particular
the frontiers cannot be empty when Fin b is inhabited.
This holds directly from c.hearly and the corrected
forward-complete ambient k-skew support. -/
theorem direction_gives_sorted_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (dir : Fin b) :
    ∃ i : Index c,
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
        CanonicalSupportWalk.next c.T c.cut dir := by
  have hbranch : SkewTree.uniqueBranchB c.T c.cut dir = true :=
    ForwardCompleteEmbedding.branch_of_height_lt
      c.T c.hcomplete c.hnon c.cut c.hcutT c.hearly dir
  let t : Node b := CanonicalSupportWalk.next c.T c.cut dir
  have hstep : SkewTree.immediateSuccB c.T c.cut t = true :=
    (CanonicalSupportWalk.next_unique c.T c.cut dir hbranch).1
  have ht : t ∈ c.T :=
    CanonicalSupportWalk.next_mem c.T c.cut dir hbranch
  have hrank : SkewTree.heightAt c.T t =
      SkewTree.heightAt c.T c.cut + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      c.T c.cut t
      (ForwardQFinalRetainedRanks.ambientT_nodup c)
      c.hcutT hstep
  have hout : ¬ ForwardAux t c.cut := by
    intro hbefore
    have hc := c.hcomplete
    simp only [SkewTree.completeB,Bool.and_eq_true] at hc
    have hle : SkewTree.heightAt c.T t ≤
        SkewTree.heightAt c.T c.cut :=
      ForwardFrontierRanks.rank_le_of_forwardAux
        c.T hc.1 c.hnon ht c.hcutT hbefore
    omega
  exact ForwardQFinalRetainedCrossing.crossing_immediate_has_sorted_frontier
    c c.cut t (cut_mem_retained c) hstep hout

/-- The actual mixed-word ambient capacity m+q<=k is
available whenever one wants to branch in any direction.
No arbitrary choice of a frontier coordinate is assumed:
the direction itself constructs a real one. -/
theorem direction_implies_ambient_capacity
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (dir : Fin b) :
    m + q ≤ k := by
  obtain ⟨i,_⟩ := direction_gives_sorted_frontier c dir
  exact ForwardQFinalMixedCapacity.local_dimension_implies_ambient_capacity
    c f i

/-- EVERY retained vertex of the exact filtered final
T'_(m+q), strictly below the final branching level,
has a genuine immediate successor in EACH ambient
direction. The ambient k-height capacity has been
eliminated from the assumptions using the real mixed
coordinate constructed from dir. -/
theorem retained_has_final_immediate_in_every_direction
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    ∃ t : Node b,
      SkewTree.immediateSuccB (finalBudgetSupport c f (m+q)).toList
        s t = true ∧
      IsPrefix (s ++ [dir]) t :=
  ForwardQFinalRetainedFullDirections.retained_has_final_immediate_in_direction
    c f (direction_implies_ambient_capacity c f dir)
    s hs hroom dir

/-- Every early retained vertex has a nonempty set of
actual immediate T'_(m+q) support successors in each
direction, with NO capacity or chosen-index premise. -/
theorem retained_branchWitnesses_nonempty_unconditional
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    SkewTree.branchWitnesses
      (finalBudgetSupport c f (m+q)).toList s dir ≠ [] :=
  ForwardQFinalRetainedFullDirections.retained_branchWitnesses_nonempty
    c f (direction_implies_ambient_capacity c f dir)
    s hs hroom dir

end DualTree.ForwardQFinalRetainedUnconditional
