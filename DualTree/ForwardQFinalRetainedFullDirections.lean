import DualTree.ForwardQFinalRetainedCrossing
import DualTree.ForwardCompleteEmbedding

/-!
# Directional branching at retained roots of the final support

The final rank-filtered support T'_(m+q) joins:
- the original complete T vertices at/before the inclusive forward cut;
- selected projected roots of the post-Ramsey mixed component words.

The source ambient support T is complete of height k. To request
an immediate T-successor for a retained s that needs another
level in T'_(m+q), we explicitly require m+q <= k. This
numerical bound must be derived from the paper's parameter
choices before the final Lemma 27 application.

Take the unique ambient T immediate successor t in direction i.
If t is retained, its edge remains immediate in the full
final support. If t crosses the cut, the previously verified
sorted-frontier replacement theorem selects the actual local
coordinate root and replaces s -> t by an immediate final
edge in the SAME ambient first direction.

Thus every retained vertex of final intrinsic rank r with
r+1<m+q has an actual final-support immediate successor in
every outgoing direction. This proves EXISTENCE, not yet
uniqueness of same-direction witnesses, so it does not
silently claim complete skewness.
-/

namespace DualTree.ForwardQFinalRetainedFullDirections

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- For each retained vertex which must branch below the final
target height, a genuine immediate successor exists in any
specified ambient direction of the FULL glued final support.
The explicit capacity m+q<=k ensures the old ambient complete
tree T still has that level available. -/
theorem retained_has_final_immediate_in_direction
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hcapacity : m + q ≤ k)
    (s : Node b)
    (hs : s ∈ retained c)
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    ∃ t : Node b,
      SkewTree.immediateSuccB (finalBudgetSupport c f (m+q)).toList
        s t = true ∧
      IsPrefix (s ++ [dir]) t := by
  classical
  have heq :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s =
        SkewTree.heightAt c.T s :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f (m+q) s hs
  have hroomT : SkewTree.heightAt c.T s + 1 < m + q := by
    simpa only [heq] using hroom
  have hroomK : SkewTree.heightAt c.T s + 1 < k := by
    omega
  have hsT : s ∈ c.T :=
    retained_subset_T c s hs
  have hbranch : SkewTree.uniqueBranchB c.T s dir = true :=
    ForwardCompleteEmbedding.branch_of_height_lt
      c.T c.hcomplete c.hnon s hsT hroomK dir
  let t : Node b := CanonicalSupportWalk.next c.T s dir
  have hnext :=
    CanonicalSupportWalk.next_unique c.T s dir hbranch
  have hstep : SkewTree.immediateSuccB c.T s t = true :=
    hnext.1
  have hdir : IsPrefix (s ++ [dir]) t :=
    hnext.2
  have htT : t ∈ c.T :=
    CanonicalSupportWalk.next_mem c.T s dir hbranch
  by_cases hbefore : ForwardAux t c.cut
  · have htRetained : t ∈ retained c := by
      classical
      exact Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr htT,hbefore⟩
    have hfinal :
        SkewTree.immediateSuccB
          (finalBudgetSupport c f (m+q)).toList s t = true :=
      ForwardQFinalRetainedEdges.retained_T_immediate_is_final_immediate
        c f (m+q) s t hs htRetained hstep
    exact ⟨t,hfinal,hdir⟩
  · obtain ⟨i,himmediate,hlabel⟩ :=
      ForwardQFinalRetainedCrossing.crossing_immediate_has_replacement_in_direction
        c f s t hs hstep hbefore hroomT dir hdir
    exact ⟨(projected c ⟨i,ForwardQFinalLocalRoots.localRoot c f i⟩).1,
      himmediate,hlabel⟩

/-- At a retained early vertex, every ambient direction has
a NONEMPTY family of immediate final-support witnesses.
This is the exact existence half of uniqueBranchB. -/
theorem retained_branchWitnesses_nonempty
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hcapacity : m + q ≤ k)
    (s : Node b)
    (hs : s ∈ retained c)
    (hroom :
      SkewTree.heightAt (finalBudgetSupport c f (m+q)).toList s + 1 <
        m + q)
    (dir : Fin b) :
    SkewTree.branchWitnesses
      (finalBudgetSupport c f (m+q)).toList s dir ≠ [] := by
  obtain ⟨t,hstep,hdir⟩ :=
    retained_has_final_immediate_in_direction
      c f hcapacity s hs hroom dir
  have hmem : t ∈
      SkewTree.branchWitnesses
        (finalBudgetSupport c f (m+q)).toList s dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      (finalBudgetSupport c f (m+q)).toList s t dir).2
        ⟨hstep,hdir⟩
  intro hnil
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

end DualTree.ForwardQFinalRetainedFullDirections
