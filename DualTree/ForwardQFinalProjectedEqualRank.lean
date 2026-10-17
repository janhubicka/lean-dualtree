import DualTree.ForwardQFinalSameFrontierLex
import DualTree.ForwardQFinalCrossBandLex
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardQFinalLocalRankGaps
import DualTree.ForwardQFinalVectorOrdering
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.PaperAuxAntisymm

/-!
# All projected/projected cases of the final skew clause II

The candidate rank-budgeted final support has genuinely selected
projected roots P_i(z) with final intrinsic rank H_i + r_i(z),
where H_i belongs to {m,m+1}. Its ambient complete T rank is
instead H_i + |z|.

For equal FINAL ranks and ordinary lexicographic order
P_i(z) <=lex P_j(w), a three-way case split is decisive:
* i=j: use the verified same-cone lex isomorphism and local
  component skew-II to compare raw local tail lengths.
* distinct coordinates and equal T frontier ranks: the
  checked cone-lex orientation forces i<j, and the actual
  vector-complete same-level axiom compares raw tail lengths.
* different frontier ranks: lex forces the rank-(m+1)
  frontier FIRST. Equality of final ranks then forces its
  local intrinsic rank to be one smaller, and the vector
  successor-level separation offsets the one-unit frontier
  rank difference.

Original T skew-II/III converts the weak inequality of the
original T ranks into a weak inequality of ambient word lengths.

No complete-skew or final f' assertion for T'_M is assumed.
-/

namespace DualTree.ForwardQFinalProjectedEqualRank

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget

/-- A numerical comparison of the actual T ranks of two
projected points transfers to ambient LENGTH when they are
also in ordinary lex order. -/
theorem projected_length_le_of_T_rank_formula_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hrank :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
          z.1.length ≤
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 +
          w.1.length)
    (hlex : FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨j,w⟩).1) :
    (projected c ⟨i,z⟩).1.length ≤
      (projected c ⟨j,w⟩).1.length := by
  apply ForwardQFinalSameFrontierLex.ambient_length_le_of_rank_le_and_lex
    c (projected c ⟨i,z⟩) (projected c ⟨j,w⟩)
  · rw [ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩,
        ForwardQFinalProjectionOrder.projected_height c ⟨j,w⟩]
    change
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
          z.1.length ≤
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 +
          w.1.length
    exact hrank
  · exact hlex

/-- For all genuinely SELECTED projected variable roots in the
actual final T'_M, EQUAL intrinsic final ranks and ordinary
lex imply nondecreasing actual ambient word lengths.
This discharges the complete new/new part of skew clause II. -/
theorem selected_projected_equal_final_rank_lex_length_le
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hw : (⟨j,w⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (heq :
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 =
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨j,w⟩).1)
    (hlex : FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨j,w⟩).1) :
    (projected c ⟨i,z⟩).1.length ≤
      (projected c ⟨j,w⟩).1.length := by
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
  have hfinal : Hi + ri = Hj + rj := by
    rw [ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M i z hz,
      ForwardQFinalIntrinsicRank.final_projected_height_formula
        c f M j w hw] at heq
    exact heq
  by_cases hindices : i = j
  · subst j
    have hlocal :
        SkewTree.heightAt
          (f.vector.components i).toVariableWord.supportNodes z.1 =
        SkewTree.heightAt
          (f.vector.components i).toVariableWord.supportNodes w.1 := by
      rw [ForwardQFinalIntrinsicRank.final_projected_height_formula
          c f M i z hz,
        ForwardQFinalIntrinsicRank.final_projected_height_formula
          c f M i w hw] at heq
      omega
    exact
      ForwardQFinalSameFrontierLex.projected_same_frontier_equal_local_rank_length_le
        c f i z w hzSupp hwSupp hlocal hlex
  · have hiBand : Hi = m ∨ Hi = m + 1 :=
      ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c i
    have hjBand : Hj = m ∨ Hj = m + 1 :=
      ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c j
    by_cases hbandEq : Hi = Hj
    · have hlocal : ri = rj := by omega
      have hindex : i < j := by
        rcases lt_trichotomy i j with hij | heqij | hji
        · exact hij
        · exact (hindices heqij).elim
        · have hfrontEq :
              SkewTree.heightAt c.T
                (ForwardOrderedProjections.frontierAt c.T c.cut j).1 =
              SkewTree.heightAt c.T
                (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
            hbandEq.symm
          have hreverse :=
            ForwardQFinalCrossBandLex.projected_lex_of_same_frontier_rank_index_lt
              c j i hji hfrontEq w z
          have heqNodes :
              (projected c ⟨i,z⟩).1 =
              (projected c ⟨j,w⟩).1 :=
            PaperAuxAntisymm.finLexLE_antisymm _ _ hlex hreverse
          have heqAddress :
              (⟨i,z⟩ : LocalAddress c) =
              (⟨j,w⟩ : LocalAddress c) :=
            (projected_injective c) (Subtype.ext heqNodes)
          exact (hindices (congrArg Sigma.fst heqAddress)).elim
      have hzNode :
          z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
        change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
        exact List.mem_map.mpr ⟨z,hzSupp,rfl⟩
      have hwNode :
          w.1 ∈ (f.vector.components j).toVariableWord.supportNodes := by
        change w.1 ∈ (f.vector.components j).support.map (fun t => t.1)
        exact List.mem_map.mpr ⟨w,hwSupp,rfl⟩
      have hriq : ri < q :=
        ForwardQFinalTwoFrontierBudget.local_component_height_lt_q
          c f i z hzSupp
      have hlen : z.1.length ≤ w.1.length :=
        ForwardQFinalVectorOrdering.local_lengths_le_of_equal_level
          c f i j hindex ri hriq z w hzNode hwNode rfl hlocal.symm
      have hnum : Hi + z.1.length ≤ Hj + w.1.length := by
        omega
      exact projected_length_le_of_T_rank_formula_le c i j z w hnum hlex
    · rcases hiBand with hi | hi
      · rcases hjBand with hj | hj
        · exact (hbandEq (by omega)).elim
        · have hreverse :=
            ForwardQFinalCrossBandLex.projected_rank_succ_lex_before_rank_m
              c i j hi hj z w
          have heqNodes :
              (projected c ⟨i,z⟩).1 =
              (projected c ⟨j,w⟩).1 :=
            PaperAuxAntisymm.finLexLE_antisymm _ _ hlex hreverse
          have heqAddress :
              (⟨i,z⟩ : LocalAddress c) =
              (⟨j,w⟩ : LocalAddress c) :=
            (projected_injective c) (Subtype.ext heqNodes)
          exact (hindices (congrArg Sigma.fst heqAddress)).elim
      · rcases hjBand with hj | hj
        · have hloc : ri < rj := by omega
          have hlen : z.1.length < w.1.length :=
            ForwardQFinalLocalRankGaps.local_length_lt_of_rank_lt
              c f i j z w hzSupp hwSupp hloc
          have hnum : Hi + z.1.length ≤ Hj + w.1.length := by
            omega
          exact projected_length_le_of_T_rank_formula_le
            c i j z w hnum hlex
        · exact (hbandEq (by omega)).elim

end DualTree.ForwardQFinalProjectedEqualRank
