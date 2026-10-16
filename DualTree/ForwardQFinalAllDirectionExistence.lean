import DualTree.ForwardQFinalRetainedUnconditional
import DualTree.ForwardQFinalProjectedFullDirections
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalSelectedPredecessors

/-!
# Full directional existence at EVERY final Lemma 27 support vertex

The exact final support T'_(m+q) consists of retained T roots
and M-budget-selected projections P_i(z). The retained case
has been proved without added numerical/index assumptions.

For a SELECTED projected vertex P_i(z), the exact final
intrinsic-rank formula is

  height_(T'_M)(P_i(z))
    = height_T(frontier_i) + height_ws(f_i)(z).

The frontier height is m or m+1. If the vertex lies
strictly below the last branching level,
height_(T'_M)(P_i(z))+1<m+q, then:

* in the rank-m frontier case local height(z)+1<q;
* in the rank-(m+1) case local height(z)+2<q.

These are EXACTLY the premises of the already checked
direction-labelled immediate successor theorems at
selected new roots. Combining them with retained
unconditional branching gives a genuine FULL-SUPPORT
immediate successor in every ambient direction from
EVERY vertex that must still branch.

This is the existence half of complete branching,
not directional uniqueness, meet closure or the
global skew/length order. The final f'/span/Ramsey
proof obligations are likewise independent.
-/

namespace DualTree.ForwardQFinalAllDirectionExistence

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut

/-- Every M-selected projected support root of sufficiently
low actual FINAL intrinsic rank has a genuine immediate
T'_M successor in any desired ambient direction. There is
no extra local-height premise: it is derived from the
verified intrinsic-rank equation and the two frontier bands. -/
theorem selected_projected_has_final_immediate_in_direction
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f (m+q))
    (hroom : SkewTree.heightAt
      (finalBudgetSupport c f (m+q)).toList
      (projected c ⟨i,z⟩).1 + 1 < m+q)
    (dir : Fin b) :
    ∃ t : Node b,
      SkewTree.immediateSuccB
        (finalBudgetSupport c f (m+q)).toList
        (projected c ⟨i,z⟩).1 t = true ∧
      IsPrefix ((projected c ⟨i,z⟩).1 ++ [dir]) t := by
  have htag :
      (⟨i,z⟩ : LocalAddress c) ∈
        taggedLocalRoots c f :=
    ((selectedLocalRoots_mem_iff c f (m+q) ⟨i,z⟩).1 hz).1
  have hzSupp : z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 htag
  have hrank :=
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f (m+q) i z hz
  have hroomRank :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 +
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 +
      1 < m+q := by
    rw [hrank] at hroom
    exact hroom
  rcases ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ
      c i with hm | hmPlus
  · have hlocal : SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 +
        1 < q := by
      rw [hm] at hroomRank
      omega
    obtain ⟨w,hw,hstep,hcone⟩ :=
      ForwardQFinalProjectedFullDirections.final_new_full_direction_rank_m
        c f i z hzSupp hm hlocal dir
    exact ⟨(projected c ⟨i,w⟩).1,hstep,hcone⟩
  · have hlocal : SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 +
        2 < q := by
      rw [hmPlus] at hroomRank
      omega
    obtain ⟨w,hw,hstep,hcone⟩ :=
      ForwardQFinalProjectedFullDirections.final_new_full_direction_rank_succ
        c f i z hzSupp hmPlus hlocal dir
    exact ⟨(projected c ⟨i,w⟩).1,hstep,hcone⟩

/-- The actual final support T'_(m+q) has a genuine
immediate support successor in every specified ambient
direction from EVERY vertex whose intrinsic FINAL rank
requires another level. This theorem is unconditionally
quantified over the genuine typed Frame and mixed word;
neither a capacity parameter nor a frontier index is
left as an added assumption. -/
theorem final_has_immediate_in_every_direction_below_last_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ finalBudgetSupport c f (m+q))
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    ∃ t : Node b,
      SkewTree.immediateSuccB
        (finalBudgetSupport c f (m+q)).toList s t = true ∧
      IsPrefix (s ++ [dir]) t := by
  classical
  rcases Finset.mem_union.mp hs with hret | hnew
  · exact
      ForwardQFinalRetainedUnconditional.retained_has_final_immediate_in_every_direction
        c f s hret hroom dir
  · obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hnew
    rcases u with ⟨i,z⟩
    have hroom' :
        SkewTree.heightAt
          (finalBudgetSupport c f (m+q)).toList
          (projected c ⟨i,z⟩).1 + 1 < m+q := by
      simpa only [heq] using hroom
    obtain ⟨t,ht,hd⟩ :=
      selected_projected_has_final_immediate_in_direction
        c f i z hu hroom' dir
    refine ⟨t,?_,?_⟩
    · simpa only [heq] using ht
    · simpa only [heq] using hd

/-- The corresponding branch-witness list is NONEMPTY
at every nonfinal-rank vertex and every ambient direction.
The separate proof of at-most-one witness remains open. -/
theorem final_branchWitnesses_nonempty_below_last_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ finalBudgetSupport c f (m+q))
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    SkewTree.branchWitnesses
      (finalBudgetSupport c f (m+q)).toList s dir ≠ [] := by
  obtain ⟨t,ht,hd⟩ :=
    final_has_immediate_in_every_direction_below_last_level
      c f s hs hroom dir
  have hmem : t ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f (m+q)).toList s dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      (finalBudgetSupport c f (m+q)).toList s t dir).2
      ⟨ht,hd⟩
  intro hnil
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

end DualTree.ForwardQFinalAllDirectionExistence
