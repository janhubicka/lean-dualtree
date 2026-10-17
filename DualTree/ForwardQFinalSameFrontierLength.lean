import DualTree.ForwardQFinalRetainedSkewLength
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardQFinalProjectionOrder
import DualTree.SkewLevelOrder
import DualTree.SupportReachability

/-!
# Strict global skew length order within each projected frontier cone

The final M-filtered Lemma 27 support contains projected roots
P_i(z) whose intrinsic final rank is the frontier's original
T rank plus the LOCAL coordinate support rank of z.

When two selected new roots come from the SAME frontier i,
strict final-rank inequality is equivalent to strict
inequality of their local q-complete support ranks.

The genuine local q-complete skew axiom (iii) gives strict
inequality of their raw local address lengths. This transfers
to strict ambient T ranks of their actual projections by the
certified P_i rank formula (which adds the same frontier rank).
Finally the ambient original T skew axiom (iii) forces strict
inequality of their actual ambient word lengths.

This proves the SAME-FRONTIER new/new part of final skew
length clause III, independently of any global skew or
completeness assertion for the joined T'_M support.

Different frontier indices, equal-rank lex comparisons
and the special skew witness remain separate obligations.
-/

namespace DualTree.ForwardQFinalSameFrontierLength

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget

/-- Two actual local q-complete variable-support roots
with different intrinsic LOCAL ranks must have strictly
ordered raw word lengths. No absolute depth/rank equality
or ambient immediate-child assumption is used. -/
theorem local_length_lt_of_rank_lt
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hw : w ∈ (f.vector.components i).support)
    (hranks :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 <
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes w.1) :
    z.1.length < w.1.length := by
  let L := (f.vector.components i).toVariableWord.supportNodes
  have hzNode : z.1 ∈ L := by
    change z.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hwNode : w.1 ∈ L := by
    change w.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hne : z.1 ≠ w.1 := by
    intro heq
    rw [heq] at hranks
    omega
  have hnon : L.length ≠ 1 :=
    SupportReachability.nonsingleton_of_distinct_members
      L hzNode hwNode hne
  have hcomp :=
    ForwardQFinalTwoFrontierBudget.local_component_complete c f i
  simp only [SkewTree.completeB, Bool.and_eq_true] at hcomp
  exact SkewLevelOrder.length_lt_of_height_lt
    L SkewTree.forwardAuxB hcomp.1 hnon
    hzNode hwNode hranks

/-- An actual selected new/new pair of STRICTLY different
FINAL intrinsic ranks in the SAME frontier necessarily has
strictly ordered ambient word lengths in the complete T.
This is exactly the same-frontier case of final skew clause III. -/
theorem selected_same_frontier_final_rank_lt_length_lt
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : (⟨i,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 <
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,w⟩).1) :
    (projected c ⟨i,z⟩).1.length <
      (projected c ⟨i,w⟩).1.length := by
  have hzLocal :
      z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1
      ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).1
  have hwLocal :
      w ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i w).1
      ((selectedLocalRoots_mem_iff c f M ⟨i,w⟩).1 hw).1
  have hlocalRank :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 <
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes w.1 := by
    rw [ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M i z hz,
      ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M i w hw] at hranks
    omega
  have hlocalLen :
      z.1.length < w.1.length :=
    local_length_lt_of_rank_lt
      c f i z w hzLocal hwLocal hlocalRank
  have hambientRank :
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 <
      SkewTree.heightAt c.T (projected c ⟨i,w⟩).1 := by
    rw [ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩,
      ForwardQFinalProjectionOrder.projected_height c ⟨i,w⟩]
    change
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        z.1.length <
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        w.1.length
    omega
  exact SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB
    (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
    c.hnon
    (projected c ⟨i,z⟩).2
    (projected c ⟨i,w⟩).2
    hambientRank

end DualTree.ForwardQFinalSameFrontierLength
