import DualTree.ForwardQFinalProjectedEqualRank
import DualTree.ForwardQFinalOldNewEqualRank
import DualTree.ForwardQFinalRetainedSkewLength

/-!
# The literal final-support skew clause II in corrected Lemma 27

For the rank-filtered final support S, the same-intrinsic-rank
ordinary-lex condition is checked on every pair in its ACTUAL
finite list. Split S into retained old T nodes and genuinely
selected new projected roots:

* retained / retained: the previously verified retained skew-II;
* retained / projected: at equal final ranks the only valid
  lex orientation is old first, and its length inequality is
  already proved;
* projected / retained: the opposite lex orientation is
  impossible at equal ranks across the disjoint corrected cut;
* projected / projected: the all-cone, both-frontier-band
  equal-rank theorem provides the required length comparison.

The four cases establish the literal Boolean condIIB for
the final support, without assuming its global skewness.
The remaining complete-skew condition is the special
branching witness IV (in addition to root/singleton bookkeeping).
The final ambient word f', span refinement, and printed
reverse-starred interface are separate obligations.
-/

namespace DualTree.ForwardQFinalSkewII

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut

/-- The EXACT final rank-budgeted corrected support satisfies
the skew same-final-intrinsic-rank ordinary-lex length
condition II, without using an assumed final skewB axiom. -/
theorem finalBudgetSupport_condIIB
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    SkewTree.condIIB
      (finalBudgetSupport c f M).toList = true := by
  classical
  let S := (finalBudgetSupport c f M).toList
  unfold SkewTree.condIIB
  apply List.all_eq_true.mpr
  intro s hs
  apply List.all_eq_true.mpr
  intro t ht
  by_cases hcond :
      SkewTree.heightAt S s = SkewTree.heightAt S t ∧
        FinLexLE s t
  · obtain ⟨hranks, hlex⟩ := hcond
    have hsFinal : s ∈ finalBudgetSupport c f M :=
      Finset.mem_toList.mp hs
    have htFinal : t ∈ finalBudgetSupport c f M :=
      Finset.mem_toList.mp ht
    change s ∈ retained c ∪ selectedProjectedRoots c f M at hsFinal
    change t ∈ retained c ∪ selectedProjectedRoots c f M at htFinal
    have hLength : s.length ≤ t.length := by
      rcases Finset.mem_union.mp hsFinal with hsRet | hsNew
      · rcases Finset.mem_union.mp htFinal with htRet | htNew
        · exact
            ForwardQFinalRetainedSkewLength.final_retained_equal_rank_lex_length_le
              c f s t hsRet htRet hranks hlex
        · obtain ⟨u, huTag, huEq, huBudget⟩ :=
            selectedProjectedRoots_budget_witness c f M t htNew
          have huSelected : u ∈ selectedLocalRoots c f M :=
            (selectedLocalRoots_mem_iff c f M u).2
              ⟨huTag, huBudget⟩
          rcases u with ⟨j,w⟩
          rw [huEq] at hranks ⊢
          exact
            ForwardQFinalOldNewEqualRank.old_new_equal_final_rank_length_le
              c f s hsRet j w huSelected hranks
      · obtain ⟨u, huTag, huEq, huBudget⟩ :=
          selectedProjectedRoots_budget_witness c f M s hsNew
        have huSelected : u ∈ selectedLocalRoots c f M :=
          (selectedLocalRoots_mem_iff c f M u).2
            ⟨huTag, huBudget⟩
        rcases u with ⟨i,z⟩
        rcases Finset.mem_union.mp htFinal with htRet | htNew
        · rw [huEq] at hranks hlex
          have hImpossible :
              ¬ FinLexLE (projected c ⟨i,z⟩).1 t :=
            ForwardQFinalOldNewEqualRank.old_new_equal_final_rank_not_lex_new_first
              c f t htRet i z huSelected hranks.symm
          exact (hImpossible hlex).elim
        · obtain ⟨v, hvTag, hvEq, hvBudget⟩ :=
            selectedProjectedRoots_budget_witness c f M t htNew
          have hvSelected : v ∈ selectedLocalRoots c f M :=
            (selectedLocalRoots_mem_iff c f M v).2
              ⟨hvTag, hvBudget⟩
          rcases v with ⟨j,w⟩
          rw [huEq, hvEq] at hranks hlex ⊢
          exact
            ForwardQFinalProjectedEqualRank.selected_projected_equal_final_rank_lex_length_le
              c f i j z w huSelected hvSelected hranks hlex
    change
      (if SkewTree.heightAt S s = SkewTree.heightAt S t ∧ FinLexLE s t
       then decide (s.length ≤ t.length)
       else true) = true
    simp [hranks, hlex, hLength]
  · change
      (if SkewTree.heightAt S s = SkewTree.heightAt S t ∧ FinLexLE s t
       then decide (s.length ≤ t.length)
       else true) = true
    simp [hcond]

end DualTree.ForwardQFinalSkewII
