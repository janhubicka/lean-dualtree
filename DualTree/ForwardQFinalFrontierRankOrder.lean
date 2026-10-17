import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalRetainedSkewLength
import DualTree.ForwardFrontierRanks
import DualTree.ForwardSortedFrontiers
import DualTree.ForwardQFinalVectorOrdering

/-!
# Strict intrinsic frontier ranks determine sorted coordinate order

The genuine corrected Lemma 27 frame uses a FORWARD length-first
ordering of its minimal outside-cut complete-tree frontiers.
The complete ambient T has the skew length clause (iii), hence
the sorted frontier list cannot place a strictly higher intrinsic
T rank before a lower rank.

This is an unconditional property of the actual Frame: it does
not require a selected local Ramsey word, its rank budget, or an
unproved globally skew final support T'_M.

In particular all rank-m minimal frontiers precede every rank-(m+1)
minimal frontier. This is one necessary interface for the remaining
mixed-frontier projected/projected skew length comparisons; it is
not by itself a proof of either final skew clause (ii) or (iii).
-/

namespace DualTree.ForwardQFinalFrontierRankOrder

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- Strictly increasing original T-ranks of two sorted outside-cut
frontiers imply strictly increasing coordinate indices. The
contrapositive uses the already checked sorted-frontier ForwardAux
order and ambient skew clause (iii). -/
theorem index_lt_of_frontier_rank_lt
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (hrank :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 <
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji | heq
  · have hordered :=
      ForwardSortedFrontiers.frontiers_get_order c.T c.cut j i hji
    change ForwardAux
      (ForwardOrderedProjections.frontierAt c.T c.cut j).1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 at hordered
    have hreverse :
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut j).1 ≤
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
      ForwardFrontierRanks.rank_le_of_forwardAux c.T
        (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
        c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut j).2
        (ForwardOrderedProjections.frontierAt c.T c.cut i).2
        hordered
    omega
  · rw [heq] at hrank
    exact (lt_irrefl _) hrank

/-- The TWO rank bands of the selected corrected frontier are in
index order: rank m first, rank m+1 second. This observation must
not be confused with an unverified assertion that the ordinary
lexicographic order of projected descendants has the same order. -/
theorem rank_m_index_lt_rank_succ
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (hi :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (hj :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 = m + 1) :
    i < j := by
  apply index_lt_of_frontier_rank_lt c i j
  omega


/-- For two ACTUAL projected support nodes attached to different
frontiers, increasing their original T frontier rank from m to m+1,
while keeping the SAME local intrinsic support rank, forces strict
ambient word-length growth. This uses the vector skew same-level
length inequality and the independent complete-T rank formula.
No final T'_M skew assumption is used. -/
theorem projected_length_lt_of_rank_m_to_succ_same_local_rank
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hi : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (hj : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut j).1 = m + 1)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z ∈ (f.vector.components i).support)
    (hw : w ∈ (f.vector.components j).support)
    (hr : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 =
      SkewTree.heightAt
        (f.vector.components j).toVariableWord.supportNodes w.1) :
    (projected c ⟨i,z⟩).1.length <
      (projected c ⟨j,w⟩).1.length := by
  have hij : i < j := rank_m_index_lt_rank_succ c i j hi hj
  have hzNode :
      z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hwNode :
      w.1 ∈ (f.vector.components j).toVariableWord.supportNodes := by
    change w.1 ∈ (f.vector.components j).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  let r := SkewTree.heightAt
    (f.vector.components i).toVariableWord.supportNodes z.1
  have hrq : r < q :=
    ForwardQFinalTwoFrontierBudget.local_component_height_lt_q
      c f i z hz
  have hlen : z.1.length ≤ w.1.length :=
    ForwardQFinalVectorOrdering.local_lengths_le_of_equal_level
      c f i j hij r hrq z w hzNode hwNode rfl hr.symm
  have hambient :
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 <
      SkewTree.heightAt c.T (projected c ⟨j,w⟩).1 := by
    rw [ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩,
      ForwardQFinalProjectionOrder.projected_height c ⟨j,w⟩]
    change
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        z.1.length <
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 +
        w.1.length
    rw [hi,hj]
    omega
  exact SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB
    (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
    c.hnon (projected c ⟨i,z⟩).2 (projected c ⟨j,w⟩).2
    hambient

end DualTree.ForwardQFinalFrontierRankOrder
