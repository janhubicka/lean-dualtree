import DualTree.ForwardQFinalRetainedSkewLength
import DualTree.ForwardQFinalRankBound
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalProjectionOrder
import DualTree.ImmediateSupportHeight

/-!
# Cross retained/projected intrinsic ranks and ambient length inequalities

The corrected Lemma 27 candidate final support T'_M combines
retained T vertices (intrinsic rank <= m) with selected projections
P_i(z) (intrinsic rank = frontier T-rank + local support rank).
Every frontier T-rank is m or m+1. Thus a selected projected
root never has LOWER intrinsic final rank than a retained vertex.

For every retained s and projected p, the ORIGINAL ambient
T-ranks are likewise nondecreasing, independently of whether
the local projected root is selected. If s <=_lex p then the
ambient word lengths obey |s| <= |p| by the original complete
T skew length conditions II/III. This directly proves the
retained-to-projected orientation of same-level clause II.

The strict final intrinsic rank inequality is stronger:
it forces strict original T-rank inequality even if the
frontier itself has rank m and the local root is deeply
stretched. To see this, a local word of positive intrinsic
rank cannot have the empty ambient address. This proves
the RETAINED -> PROJECTED clause III for all genuinely
selected new vertices.

These statements do NOT establish the reverse-lex orientation
for equal-rank NEW -> OLD pairs, the new/new global comparisons,
or the special skew branching witness IV. They are partial
lemmas, not a complete-skew or final Ramsey proof.
-/

namespace DualTree.ForwardQFinalCrossRankLength

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- The ambient complete T rank of any retained vertex
is no larger than the ambient T rank of any projected
local address, even before applying the final filter. -/
theorem retained_ambient_rank_le_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1))) :
    SkewTree.heightAt c.T s ≤
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 := by
  have hret :=
    ForwardQFinalRankBound.retained_T_rank_le_cut_rank c s hs
  have hproject :=
    ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩
  rcases ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ
      c i with hsame | hsucc
  · rw [hproject,hsame]
    omega
  · rw [hproject,hsucc]
    omega

/-- In particular when a retained node is forward-lex
before a projected node, its AMBIENT word length cannot
exceed that of the projection. This is the old/new
orientation of the final same-intrinsic-rank clause II,
and does not even need an intrinsic-rank equality. -/
theorem retained_lex_projected_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hlex : FinLexLE s (projected c ⟨i,z⟩).1) :
    s.length ≤ (projected c ⟨i,z⟩).1.length := by
  let t := (projected c ⟨i,z⟩).1
  have hle : SkewTree.heightAt c.T s ≤
      SkewTree.heightAt c.T t :=
    retained_ambient_rank_le_projected c s hs i z
  by_cases heq : SkewTree.heightAt c.T s =
      SkewTree.heightAt c.T t
  · have hrow :=
      (List.all_eq_true.mp
        (ForwardQFinalRetainedSkewLength.ambient_condIIB c))
        s (retained_subset_T c s hs)
    have hcell :=
      (List.all_eq_true.mp hrow) t (projected c ⟨i,z⟩).2
    change FinLexLE s t at hlex
    change s.length ≤ t.length
    have hor : ¬ FinLexLE s t ∨ s.length ≤ t.length := by
      simpa only [heq] using hcell
    exact hor.resolve_left hlex
  · have hlt : SkewTree.heightAt c.T s <
        SkewTree.heightAt c.T t := by omega
    exact Nat.le_of_lt
      (SkewLevelOrder.length_lt_of_height_lt
        c.T SkewTree.forwardAuxB
        (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
        c.hnon
        (retained_subset_T c s hs)
        (projected c ⟨i,z⟩).2 hlt)

/-- A selected new projected root has intrinsic FINAL
support rank at least that of every retained old vertex.
The rank band m/m+1 is essential, not ambient word depth. -/
theorem selected_final_rank_retained_le_projected
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList s ≤
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1 := by
  rw [
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs,
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i z hz]
  have hret :=
    ForwardQFinalRankBound.retained_T_rank_le_cut_rank c s hs
  rcases ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ
      c i with hsame | hsucc
  · rw [hsame]
    omega
  · rw [hsucc]
    omega

/-- A LOCAL support node of positive intrinsic support
rank must be a nonempty ambient word. Holds even if its
support is not prefix-closed as an ambient set. -/
theorem local_positive_rank_forces_nonempty
    {b : Nat}
    (S : List (Node b))
    (z : Node b)
    (hpos : 0 < SkewTree.heightAt S z) :
    0 < z.length := by
  cases z with
  | nil =>
      have hzero : SkewTree.heightAt S ([] : Node b) = 0 :=
        ImmediateSupportHeight.heightAt_root_zero
          S ([] : Node b) (by
            intro t _
            exact ⟨t,by simp⟩)
      omega
  | cons i tail =>
      simp

/-- If a retained vertex has strictly smaller FINAL
intrinsic rank than a selected new projected vertex,
their ambient lengths are STRICTLY ordered. This is
the cross old/new orientation of final skew clause III.
No matching of local variable names into old roots occurs. -/
theorem retained_lower_final_rank_projected_length_lt
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hrank :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s <
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1) :
    s.length < (projected c ⟨i,z⟩).1.length := by
  let localRank :=
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1
  let frontierRank :=
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have hretBound :=
    ForwardQFinalRankBound.retained_T_rank_le_cut_rank c s hs
  have hfinalOld :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs
  have hfinalNew :=
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i z hz
  have hfinalStrict :
      SkewTree.heightAt c.T s < frontierRank + localRank := by
    rw [hfinalOld,hfinalNew] at hrank
    exact hrank
  have hproj :
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 =
      frontierRank + z.1.length :=
    ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩
  have hband : frontierRank = m ∨ frontierRank = m + 1 :=
    ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c i
  have hambientStrict :
      SkewTree.heightAt c.T s <
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 := by
    rw [hproj]
    rcases hband with hsame | hsucc
    · rw [hsame]
      by_cases hlocPos : 0 < localRank
      · have hzpos : 0 < z.1.length :=
          local_positive_rank_forces_nonempty
            (f.vector.components i).toVariableWord.supportNodes
            z.1 hlocPos
        omega
      · have hzero : localRank = 0 := by omega
        omega
    · rw [hsucc]
      omega
  exact SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB
    (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
    c.hnon (retained_subset_T c s hs)
    (projected c ⟨i,z⟩).2 hambientStrict

end DualTree.ForwardQFinalCrossRankLength
