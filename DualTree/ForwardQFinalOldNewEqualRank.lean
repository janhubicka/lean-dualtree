import DualTree.ForwardQFinalCrossRankLength
import DualTree.ForwardQFinalFrontierLex

/-!
# The exact old/new equal-rank skew length case of the final T'_M

The retained/projected final intrinsic rank comparison shows
that selected projected roots never have final rank smaller
than a retained old vertex. If their final ranks are EQUAL,
both ranks must be the distinguished cut rank m, the
frontier of the projected vertex also has ambient T-rank m,
and the projected local root has LOCAL rank zero.

The previously verified frontier lex geometry then says
the retained old vertex is lex BEFORE every projected
descendant of that rank-m frontier. Reversed lex order
is impossible because the two vertices belong to
disjoint sides of the inclusive cut.

This settles the entire retained/projected equal-final-rank
length comparison for the global repaired skew clause II:
only the old-before-new lex case is possible, and the
original ambient T skew II/III already gives the
required nondecreasing ambient lengths.

It does NOT settle equal-rank new/new pairs from different
frontiers, strictly ordered new/new pairs across frontiers,
or skew witness IV.
-/

namespace DualTree.ForwardQFinalOldNewEqualRank

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- Equal final intrinsic ranks in an old/new selected pair
force BOTH vertices to lie at rank m, the selected frontier
to have T-rank m and the local root to have intrinsic
coordinate rank zero. The upper m+1 frontiers cannot
contribute an old/new equality case. -/
theorem old_new_equal_final_rank_forces_cut_level
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (heq :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s =
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1) :
    SkewTree.heightAt c.T s = m ∧
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m ∧
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = 0 := by
  have hretBound :=
    ForwardQFinalRankBound.retained_T_rank_le_cut_rank c s hs
  rw [
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs,
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i z hz] at heq
  rcases ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ
      c i with hsame | hsucc
  · rw [hsame] at heq
    constructor
    · omega
    constructor
    · exact hsame
    · omega
  · rw [hsucc] at heq
    omega

/-- Equality of final rank in the old/new case forces
the ACTUAL corrected forward lex order: old retained
first, new projection second. This uses rank-m
frontier geometry, not a false general claim that
length-first sorted frontiers are lex-sorted. -/
theorem old_new_equal_final_rank_lex_old_first
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (heq :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s =
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1) :
    FinLexLE s (projected c ⟨i,z⟩).1 := by
  obtain ⟨hsRank, hfrontRank, _⟩ :=
    old_new_equal_final_rank_forces_cut_level
      c f s hs i z hz heq
  exact ForwardQFinalFrontierLex.retained_rank_m_lex_before_projected_rank_m
    c s hs hsRank i hfrontRank z

/-- Reversed lex ordering of a projected new root before
an old retained vertex at the same final intrinsic rank
is IMPOSSIBLE. An assumed reversal plus the verified
old-before-new comparison would identify the two nodes,
contradicting retained/projected cut disjointness. -/
theorem old_new_equal_final_rank_not_lex_new_first
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (heq :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s =
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1) :
    ¬ FinLexLE (projected c ⟨i,z⟩).1 s := by
  intro hnewOld
  have holdNew :=
    old_new_equal_final_rank_lex_old_first
      c f s hs i z hz heq
  have hsame :
      (projected c ⟨i,z⟩).1 = s :=
    PaperAuxAntisymm.finLexLE_antisymm
      (projected c ⟨i,z⟩).1 s hnewOld holdNew
  have hsBefore : ForwardAux s c.cut :=
    (Finset.mem_filter.mp hs).2
  have hprojBefore : ForwardAux
      (projected c ⟨i,z⟩).1 c.cut := by
    rw [hsame]
    exact hsBefore
  exact (ForwardQFinalSupportCut.projected_outside_cut
    c ⟨i,z⟩) hprojBefore

/-- Full old/new EQUAL final rank skew length comparison:
the only possible lex orientation is retained -> projected,
and its ambient lengths are nondecreasing. -/
theorem old_new_equal_final_rank_length_le
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (heq :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s =
      SkewTree.heightAt (finalBudgetSupport c f M).toList
        (projected c ⟨i,z⟩).1) :
    s.length ≤ (projected c ⟨i,z⟩).1.length :=
  ForwardQFinalCrossRankLength.retained_lex_projected_length_le
    c s hs i z
    (old_new_equal_final_rank_lex_old_first
      c f s hs i z hz heq)

end DualTree.ForwardQFinalOldNewEqualRank
