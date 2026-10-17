import DualTree.ForwardQFinalLocalRankGaps
import DualTree.ForwardQFinalFrontierRankOrder
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardQFinalRetainedSkewLength

/-!
# Final skew clause III: all projected/projected root pairs

The exact final support height formula for selected projected
roots is H_i + r_i, with H_i equal to m or m+1 and r_i the
LOCAL variable-support rank. The ambient complete T height of
the same root is instead H_i + |z_i|.

We convert a strict inequality of FINAL support ranks into a
strict inequality of original T ranks, handling all four possible
ordered pairs of frontier-rank bands. The reverse-band case uses
the certified quantitative TWO-level local length gap; the
forward-band equal-local-rank case uses the indexed vector
same-level ordering. No global skew property is assumed of the
final glued support.

Finally the genuine complete ambient T's skew clause III
transfers the strict T-rank inequality to actual ambient word
lengths. This proves the entire selected new/new contribution
to final skew clause III. Final skew clause II (equal intrinsic
levels with ordinary lex), special skew witness IV, and the
stitched ambient word f' remain separate.
-/

namespace DualTree.ForwardQFinalProjectedStrictSkew

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget

/-- Any two genuinely selected new roots with STRICT final
intrinsic support ranks have their actual projected vertices
strictly ordered already in the original complete T ranks.
The proof uses no final skew assumption. -/
theorem projected_T_rank_lt_of_final_rank_lt
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : (⟨j,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 <
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨j,w⟩).1) :
    SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 <
    SkewTree.heightAt c.T (projected c ⟨j,w⟩).1 := by
  have hzSupp : z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1
      ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).1
  have hwSupp : w ∈ (f.vector.components j).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f j w).1
      ((selectedLocalRoots_mem_iff c f M ⟨j,w⟩).1 hw).1
  let Hi := SkewTree.heightAt c.T
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  let Hj := SkewTree.heightAt c.T
    (ForwardOrderedProjections.frontierAt c.T c.cut j).1
  let ri := SkewTree.heightAt
    (f.vector.components i).toVariableWord.supportNodes z.1
  let rj := SkewTree.heightAt
    (f.vector.components j).toVariableWord.supportNodes w.1
  have hfinal : Hi + ri < Hj + rj := by
    rw [ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M i z hz,
      ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M j w hw] at hranks
    exact hranks
  have hTi :
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 =
        Hi + z.1.length :=
    ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩
  have hTj :
      SkewTree.heightAt c.T (projected c ⟨j,w⟩).1 =
        Hj + w.1.length :=
    ForwardQFinalProjectionOrder.projected_height c ⟨j,w⟩
  rw [hTi, hTj]
  have hiBand : Hi = m ∨ Hi = m + 1 :=
    ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c i
  have hjBand : Hj = m ∨ Hj = m + 1 :=
    ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c j
  rcases hiBand with hi | hi
  · rcases hjBand with hj | hj
    · have hloc : ri < rj := by
        rw [hi, hj] at hfinal
        omega
      have hlen : z.1.length < w.1.length :=
        ForwardQFinalLocalRankGaps.local_length_lt_of_rank_lt
          c f i j z w hzSupp hwSupp hloc
      rw [hi, hj]
      omega
    · have hrle : ri ≤ rj := by
        rw [hi, hj] at hfinal
        omega
      rcases lt_or_eq_of_le hrle with hlt | heq
      · have hlen : z.1.length < w.1.length :=
          ForwardQFinalLocalRankGaps.local_length_lt_of_rank_lt
            c f i j z w hzSupp hwSupp hlt
        rw [hi, hj]
        omega
      · have hij : i < j :=
          ForwardQFinalFrontierRankOrder.rank_m_index_lt_rank_succ
            c i j hi hj
        have hzNode :
            z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
          change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
          exact List.mem_map.mpr ⟨z, hzSupp, rfl⟩
        have hwNode :
            w.1 ∈ (f.vector.components j).toVariableWord.supportNodes := by
          change w.1 ∈ (f.vector.components j).support.map (fun t => t.1)
          exact List.mem_map.mpr ⟨w, hwSupp, rfl⟩
        have hriq : ri < q :=
          ForwardQFinalTwoFrontierBudget.local_component_height_lt_q
            c f i z hzSupp
        have hlen : z.1.length ≤ w.1.length :=
          ForwardQFinalVectorOrdering.local_lengths_le_of_equal_level
            c f i j hij ri hriq z w hzNode hwNode rfl heq.symm
        rw [hi, hj]
        omega
  · rcases hjBand with hj | hj
    · have hgap : ri + 2 ≤ rj := by
        rw [hi, hj] at hfinal
        omega
      have hlen : z.1.length + 2 ≤ w.1.length :=
        ForwardQFinalLocalRankGaps.local_length_add_two_le_of_rank_gap_two
          c f i j z w hzSupp hwSupp hgap
      rw [hi, hj]
      omega
    · have hloc : ri < rj := by
        rw [hi, hj] at hfinal
        omega
      have hlen : z.1.length < w.1.length :=
        ForwardQFinalLocalRankGaps.local_length_lt_of_rank_lt
          c f i j z w hzSupp hwSupp hloc
      rw [hi, hj]
      omega

/-- The ENTIRE selected new/new case of the corrected
final skew clause III: a strict final support rank comparison
implies STRICT ambient word-length comparison, even across
distinct, oppositely ranked frontier cones. -/
theorem selected_projected_final_rank_lt_length_lt
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : (⟨j,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 <
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨j,w⟩).1) :
    (projected c ⟨i,z⟩).1.length <
      (projected c ⟨j,w⟩).1.length :=
  SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB
    (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
    c.hnon
    (projected c ⟨i,z⟩).2
    (projected c ⟨j,w⟩).2
    (projected_T_rank_lt_of_final_rank_lt
      c f i j z w hz hw hranks)

end DualTree.ForwardQFinalProjectedStrictSkew
