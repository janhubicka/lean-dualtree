import DualTree.ForwardQFinalEnlargedInducedEvaluation
import DualTree.ForwardQFinalEnlargedCompleteWord
import DualTree.ForwardQAmbientFibreLegalWord

/-!
# The induced Q tree lies in the final support when q is at least two

The enlarged induced input marks the canonical rank-zero root of each
local component. Every ambient frontier has rank m or m+1, so all these
marked roots survive the final budget m+q when q >= 2. The other Q
vertices form the old signature base, which is retained before the cut.

This proves containment of the entire starred Q tree in the actual
interpolated word's support, including its marked leaves. It applies to
every final-root assignment and keeps genuine fixed auxiliary letters
in the local words. The q >= 2 requirement concerns the upper frontier
rank; it is not replaced by mere positivity of q.
-/

namespace DualTree.ForwardQFinalInducedSupport

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalLocalRoots
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQEnlargedConstantWords
open ForwardQAmbientFibreLegalWord

/-- At either possible ambient frontier rank, the canonical local
component root survives the final support truncation when q >= 2. -/
theorem localRoot_mem_selectedProjectedRoots_of_two_le_q
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hq : 2 ≤ q)
    (i : ForwardQFinalRefinementRoots.Index c) :
    (projected c ⟨i, localRoot c f i⟩).1 ∈
      selectedProjectedRoots c f (m+q) := by
  rcases ForwardQFinalTwoFrontierBudget.frontier_rank_cut_or_succ c i with
    hfront | hfront
  · exact rank_m_frontier_has_selected_root c f i hfront
  · exact rank_succ_frontier_has_selected_root_of_two_le_q
      c f i hfront hq

/-- The entire Q node set of an enlarged induced input is contained
in the budgeted final support. Only its marker positions enter this
geometric statement, so the final-root assignment is unrestricted. -/
theorem enlargedInducedInput_nodes_subset_finalBudgetSupport
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 2 ≤ q) :
    nodes g.core (eraseAux g.core fallback
      (enlargedInducedInput g f fallback σ)) ⊆
        finalBudgetSupport g.core f (m+q) := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with hOld | hMarked
  · exact Finset.mem_union.mpr (Or.inl
      (ForwardQFinalSupportCut.oldBase_mem_retained g.core t
        (List.mem_toFinset.mp hOld)))
  · rcases Finset.mem_image.mp hMarked with ⟨i, _, rfl⟩
    apply Finset.mem_union.mpr
    right
    change
      (projected g.core ⟨i.1, localRoot g.core f i.1⟩).1 ∈
        selectedProjectedRoots g.core f (m+q)
    exact localRoot_mem_selectedProjectedRoots_of_two_le_q
      g.core f hq i.1

/-- Every vertex of the genuine induced starred Q word belongs to
the actual enlarged final word's support. The positive-height proof
only constructs the starred input; the stronger q >= 2 hypothesis
ensures that its marked leaves survive the support truncation. -/
theorem fibreQStarredWord_enlargedInduced_tree_subset_finalWordSupport
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hqPos : 0 < q)
    (hq : 2 ≤ q) :
    ∀ t, t ∈ (fibreQStarredWord hb g fallback
      (enlargedInducedStarredInput g f fallback σ hqPos)).tree →
        t ∈ (enlargedInterpolatedFinalWord g f fallback).supportNodes := by
  classical
  intro t ht
  apply (ForwardQFinalEnlargedCompleteWord.enlargedInterpolatedFinalWord_supportNodes_iff
    g f fallback t).2
  apply enlargedInducedInput_nodes_subset_finalBudgetSupport
    g f fallback σ hq
  rw [fibreQStarredWord_tree] at ht
  exact Finset.mem_toList.mp ht

end DualTree.ForwardQFinalInducedSupport
