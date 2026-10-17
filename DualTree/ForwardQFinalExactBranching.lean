import DualTree.ForwardQFinalRetainedDirectionUniqueness
import DualTree.ForwardQFinalProjectedDirectionUniqueness
import DualTree.ForwardQFinalAllDirectionExistence
import DualTree.Lemma27QBranchCount

/-!
# Exact direction-labelled branching below the last final-support level

The verified corrected Lemma 27 final support T'_M has an exact
disjoint decomposition into retained ambient vertices and the
rank-budget-selected projections P_i(z).

The two independently proved converse/uniqueness results show:
* a RETAINED vertex has at most one immediate final successor
  in any ambient direction (ambient T meet closure + frontier
  replacement uniqueness);
* a PROJECTED vertex likewise has at most one immediate final
  successor in each ambient direction (local complete support
  meet closure + exact projected child/direction reflection).

Therefore the whole final support has AtMostOneDirection without
assuming its skew or meet-closure properties as hypotheses.

We also prove the reusable fact that, in a duplicate-free finite
support, an at-most-one-direction hypothesis combined with an
actually nonempty directional witness list forces uniqueBranchB.
The already checked final support existence theorem supplies
nonempty witnesses at EVERY rank r satisfying r+1<M.

Consequently at all such vertices we now have exactly one
immediate successor in each of b directions, and hence exactly b
immediate successors total.

This establishes the full BRANCHING AT EARLY LEVELS, not yet
the last-leaf condition or the global skew rank/ambient-length
ordering; the final ambient variable word f' remains open.
-/

namespace DualTree.ForwardQFinalExactBranching

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut

/-- General reusable conversion: in a duplicate-free support,
if each first direction has at most one immediate child and
the direction is witnessed, then exactly one child occurs,
as expressed by the executable uniqueBranchB predicate. -/
theorem uniqueBranchB_of_nonempty_atMostOne
    {b : Nat}
    (S : List (Node b))
    (hnd : S.Nodup)
    (hunique : MeetClosedFromBranching.AtMostOneDirection S)
    (s : Node b) (hs : s ∈ S) (dir : Fin b)
    (hnon : SkewTree.branchWitnesses S s dir ≠ []) :
    SkewTree.uniqueBranchB S s dir = true := by
  have hndW : (SkewTree.branchWitnesses S s dir).Nodup := by
    unfold SkewTree.branchWitnesses
    exact hnd.filter _
  cases hlist : SkewTree.branchWitnesses S s dir with
  | nil =>
      exact False.elim (hnon hlist)
  | cons x xs =>
      cases xs with
      | nil =>
          simp [SkewTree.uniqueBranchB, hlist]
      | cons y ys =>
          have hnd' : (x :: y :: ys).Nodup := by
            simpa only [hlist] using hndW
          have hxy : x ≠ y := by
            intro heq
            exact (List.nodup_cons.mp hnd').1 (by simp [heq])
          have hx : x ∈ SkewTree.branchWitnesses S s dir := by
            simp [hlist]
          have hy : y ∈ SkewTree.branchWitnesses S s dir := by
            simp [hlist]
          exact False.elim (hxy (hunique s hs dir x y hx hy))

/-- In the genuine corrected final T'_M support, EVERY
retained and selected projected vertex has at most one
immediate successor in each ambient first direction.
No global skewness, meet closure, or completeB hypothesis
is made on the final joined support itself. -/
theorem final_atMostOneDirection
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    MeetClosedFromBranching.AtMostOneDirection
      (finalBudgetSupport c f (m+q)).toList := by
  classical
  intro s hs dir x y hx hy
  have hsFin : s ∈ finalBudgetSupport c f (m+q) :=
    Finset.mem_toList.mp hs
  rcases Finset.mem_union.mp hsFin with hret | hnew
  · exact
      ForwardQFinalRetainedDirectionUniqueness.retained_atMostOneDirection
        c f (m+q) s hret dir x y hx hy
  · obtain ⟨u,hu,hnode⟩ := Finset.mem_image.mp hnew
    rcases u with ⟨i,z⟩
    have hx' : x ∈ SkewTree.branchWitnesses
        (finalBudgetSupport c f (m+q)).toList
        (projected c ⟨i,z⟩).1 dir := by
      simpa only [hnode] using hx
    have hy' : y ∈ SkewTree.branchWitnesses
        (finalBudgetSupport c f (m+q)).toList
        (projected c ⟨i,z⟩).1 dir := by
      simpa only [hnode] using hy
    exact
      ForwardQFinalProjectedDirectionUniqueness.selected_projected_atMostOneDirection
        c f (m+q) i z hu dir x y hx' hy'

/-- Every final-support vertex at intrinsic rank r with
r+1<m+q has EXACTLY ONE immediate support successor in
every literal ambient first direction. This combines
verified existence with independently verified uniqueness. -/
theorem final_uniqueBranchB_below_last_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ finalBudgetSupport c f (m+q))
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m+q)
    (dir : Fin b) :
    SkewTree.uniqueBranchB
      (finalBudgetSupport c f (m+q)).toList s dir = true := by
  exact uniqueBranchB_of_nonempty_atMostOne
    (finalBudgetSupport c f (m+q)).toList
    (Finset.nodup_toList (finalBudgetSupport c f (m+q)))
    (final_atMostOneDirection c f)
    s (Finset.mem_toList.mpr hs) dir
    (ForwardQFinalAllDirectionExistence.final_branchWitnesses_nonempty_below_last_level
      c f s hs hroom dir)

/-- The COMPLETE quantitative early branching clause:
every nonlast-rank vertex in the exact T'_M has precisely b
immediate support successors, one for each ambient direction.
This counts support successors, NOT ambient one-letter children. -/
theorem final_immediateSuccs_length_eq_b_below_last
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ finalBudgetSupport c f (m+q))
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m+q) :
    (SkewTree.immediateSuccs
      (finalBudgetSupport c f (m+q)).toList s).length = b := by
  exact Lemma27QBranchCount.immediateSuccs_length_eq_of_full_directions
    (finalBudgetSupport c f (m+q)).toList
    (Finset.nodup_toList (finalBudgetSupport c f (m+q)))
    s (fun dir => final_uniqueBranchB_below_last_level
      c f s hs hroom dir)

end DualTree.ForwardQFinalExactBranching
