import DualTree.ForwardQFinalProjectedStrictSkew
import DualTree.ForwardQFinalCrossRankLength
import DualTree.ForwardQFinalRetainedSkewLength

/-!
# Full final-support skew clause III in the corrected Lemma 27

The exact final rank-budgeted support S is a disjoint union of:
* retained complete-T vertices at/before the repaired forward cut,
* selected projected local variable roots beyond the cut.

Every support-vertex pair of strictly increasing FINAL intrinsic
ranks falls into four cases. The retained/retained and
retained/projected cases were proved previously. The
projected/retained case is IMPOSSIBLE: all selected projected
roots have final intrinsic ranks at least every retained root.
The projected/projected case was checked with full two-frontier
rank arithmetic in ForwardQFinalProjectedStrictSkew.

Here we assemble those source-facing results into the literal
Boolean condition `SkewTree.condIIIB S.toList = true`. This is
a genuine property of the actual final support, NOT an assumed
global skew hypothesis.

Clause II (equal-rank ordinary-lex lengths) and clause IV
(the special last branching witness) still need proof before
the full final `skewB`/completeB statement is established.
-/

namespace DualTree.ForwardQFinalSkewIII

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut

/-- The complete rank-filtered final Lemma 27 support satisfies
the ACTUAL skew clause III: whenever final intrinsic rank
increases, the ambient word length strictly increases.
All four membership cases are discharged without appealing
to an unproved final skew statement. -/
theorem finalBudgetSupport_condIIIB
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    SkewTree.condIIIB
      (finalBudgetSupport c f M).toList = true := by
  classical
  let S := (finalBudgetSupport c f M).toList
  unfold SkewTree.condIIIB
  apply List.all_eq_true.mpr
  intro s hs
  apply List.all_eq_true.mpr
  intro t ht
  by_cases hRanks :
      SkewTree.heightAt S s < SkewTree.heightAt S t
  · have hsFinal : s ∈ finalBudgetSupport c f M :=
      Finset.mem_toList.mp hs
    have htFinal : t ∈ finalBudgetSupport c f M :=
      Finset.mem_toList.mp ht
    change s ∈ retained c ∪ selectedProjectedRoots c f M at hsFinal
    change t ∈ retained c ∪ selectedProjectedRoots c f M at htFinal
    have hLength : s.length < t.length := by
      rcases Finset.mem_union.mp hsFinal with hsRet | hsNew
      · rcases Finset.mem_union.mp htFinal with htRet | htNew
        · exact
            ForwardQFinalRetainedSkewLength.final_retained_lower_rank_length_lt
              c f s t hsRet htRet hRanks
        · obtain ⟨u, huTag, huEq, huBudget⟩ :=
            selectedProjectedRoots_budget_witness c f M t htNew
          have huSelected : u ∈ selectedLocalRoots c f M :=
            (selectedLocalRoots_mem_iff c f M u).2
              ⟨huTag, huBudget⟩
          rcases u with ⟨j,w⟩
          rw [huEq] at hRanks ⊢
          exact
            ForwardQFinalCrossRankLength.retained_lower_final_rank_projected_length_lt
              c f s hsRet j w huSelected hRanks
      · obtain ⟨u, huTag, huEq, huBudget⟩ :=
          selectedProjectedRoots_budget_witness c f M s hsNew
        have huSelected : u ∈ selectedLocalRoots c f M :=
          (selectedLocalRoots_mem_iff c f M u).2
            ⟨huTag, huBudget⟩
        rcases u with ⟨i,z⟩
        rcases Finset.mem_union.mp htFinal with htRet | htNew
        · rw [huEq] at hRanks
          have hImpossible :
              SkewTree.heightAt S t ≤
                SkewTree.heightAt S (projected c ⟨i,z⟩).1 := by
            simpa only [S] using
              (ForwardQFinalCrossRankLength.selected_final_rank_retained_le_projected
                c f t htRet i z huSelected)
          omega
        · obtain ⟨v, hvTag, hvEq, hvBudget⟩ :=
            selectedProjectedRoots_budget_witness c f M t htNew
          have hvSelected : v ∈ selectedLocalRoots c f M :=
            (selectedLocalRoots_mem_iff c f M v).2
              ⟨hvTag, hvBudget⟩
          rcases v with ⟨j,w⟩
          rw [huEq, hvEq] at hRanks ⊢
          exact
            ForwardQFinalProjectedStrictSkew.selected_projected_final_rank_lt_length_lt
              c f i j z w huSelected hvSelected hRanks
    change
      (if SkewTree.heightAt S s < SkewTree.heightAt S t
       then decide (s.length < t.length)
       else true) = true
    simp [hRanks, hLength]
  · change
      (if SkewTree.heightAt S s < SkewTree.heightAt S t
       then decide (s.length < t.length)
       else true) = true
    simp [hRanks]

end DualTree.ForwardQFinalSkewIII
