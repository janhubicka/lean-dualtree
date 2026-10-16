import DualTree.ForwardQFinalRankBound
import DualTree.ForwardFrontierRanks
import DualTree.ForwardQFinalSelectedPredecessors

/-!
# The two possible frontier ranks and their exact local cutoffs

In the corrected forward Lemma 27, the distinguished original cut
has intrinsic ambient T-rank m and each minimal outside-cut
frontier has T-rank either m or m+1.

The local mixed-product variable word f supplied by Corollary 22
has dimension q, while the FINAL target height is M=m+q.
Consequently the printed selected-root condition

    height_(ws(f_i))(z) + height_T(frontier_i) < M

means:
  - at a rank-m frontier EVERY genuine f_i support root is selected;
  - at a rank-(m+1) frontier a genuine root is selected iff
    its local intrinsic rank + 1 < q.

The second frontier is one level shorter, and q=1 makes its
selected local root set EMPTY. Conflating the two frontiers
would give an incorrect branching/completeness proof.

The component completeness and rank bounds are derived from
the ACTUAL vectorCompleteB invariant of the mixed word f.
These are not hypotheses smuggled into the final argument.
No global skew/branching theorem is claimed by this module.
-/

namespace DualTree.ForwardQFinalTwoFrontierBudget

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget

/-- Every corrected minimal outside-cut T frontier has one
of exactly two ambient T-ranks, the cut rank m or m+1. -/
theorem frontier_rank_cut_or_succ
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m ∨
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m + 1 := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hband := ForwardFrontierRanks.frontier_rank_band
    c.T hc.1 c.hnon c.cut
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1
    c.hcutT
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i)
  simpa only [c.hm] using hband

/-- The actual f_i component of a vector-complete mixed word
has the promised q-complete forward-skew support. -/
theorem local_component_complete
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    SkewTree.completeB SkewTree.forwardAuxB q
      (f.vector.components i).toVariableWord.supportNodes = true := by
  have hparts := f.vector.vector_complete
  simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true] at hparts
  exact (List.all_eq_true.mp hparts.1) i
    (DirectionalSupport.mem_allFin _ i)

/-- Every genuine local component support root has intrinsic
rank strictly below the local mixed Ramsey dimension q. -/
theorem local_component_height_lt_q
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : z ∈ (f.vector.components i).support) :
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 < q := by
  have hzNode :
      z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  exact ForwardCompleteBijection.support_height_lt_k
    _ (local_component_complete c f i) z.1 hzNode

/-- At a rank-m frontier, the strict target budget M=m+q
accepts EVERY genuine local component variable root. -/
theorem selected_of_rank_m_frontier
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (hz : z ∈ (f.vector.components i).support) :
    (⟨i,z⟩ : LocalAddress c) ∈ selectedLocalRoots c f (m+q) := by
  have hlt := local_component_height_lt_q c f i z hz
  have hbudget : FitsTargetHeight c f (m+q) ⟨i,z⟩ := by
    change SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 +
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 < m+q
    rw [hfront]
    omega
  exact (selectedLocalRoots_mem_iff c f (m+q) ⟨i,z⟩).2
    ⟨(ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
       c f i z).2 hz, hbudget⟩

/-- Exact membership of selected local root tags at
frontiers of rank m: there is NO additional truncation. -/
theorem selected_rank_m_iff_support
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m) :
    ((⟨i,z⟩ : LocalAddress c) ∈ selectedLocalRoots c f (m+q)) ↔
      z ∈ (f.vector.components i).support := by
  constructor
  · intro hz
    have htag :=
      ((selectedLocalRoots_mem_iff c f (m+q) ⟨i,z⟩).1 hz).1
    exact (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 htag
  · exact selected_of_rank_m_frontier c f i z hfront

/-- At a rank-(m+1) frontier the target budget is ONE
LOCAL INTRINSIC LEVEL SHORTER than at rank-m frontiers. -/
theorem selected_rank_succ_iff
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m+1) :
    ((⟨i,z⟩ : LocalAddress c) ∈ selectedLocalRoots c f (m+q)) ↔
      z ∈ (f.vector.components i).support ∧
        SkewTree.heightAt
          (f.vector.components i).toVariableWord.supportNodes z.1 +
          1 < q := by
  constructor
  · intro hz
    obtain ⟨htag, hbudget⟩ :=
      (selectedLocalRoots_mem_iff c f (m+q) ⟨i,z⟩).1 hz
    have hzSupp :=
      (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
        c f i z).1 htag
    have hrank : SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 + 1 < q := by
      change SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 +
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 < m+q
        at hbudget
      rw [hfront] at hbudget
      omega
    exact ⟨hzSupp, hrank⟩
  · rintro ⟨hzSupp, hrank⟩
    have hbudget : FitsTargetHeight c f (m+q) ⟨i,z⟩ := by
      change SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 +
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 < m+q
      rw [hfront]
      omega
    exact (selectedLocalRoots_mem_iff c f (m+q) ⟨i,z⟩).2
      ⟨(ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
         c f i z).2 hzSupp,hbudget⟩

/-- When q≤1, rank-(m+1) frontiers have NO selected new
roots at all. This degenerate case must be allowed for
the M=m+1 final support instead of inventing descendants. -/
theorem no_selected_at_succ_frontier_of_q_le_one
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m+1)
    (hq : q ≤ 1) :
    (⟨i,z⟩ : LocalAddress c) ∉ selectedLocalRoots c f (m+q) := by
  intro hz
  have hrank :=
    ((selected_rank_succ_iff c f i z hfront).1 hz).2
  omega

end DualTree.ForwardQFinalTwoFrontierBudget
