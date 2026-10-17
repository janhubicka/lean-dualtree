import DualTree.ForwardQFinalFrontierLex
import DualTree.ForwardCompleteRankPredecessor
import DualTree.ForwardProjectedTerminalOrder
import DualTree.ForwardQFinalRetainedSkewLength

/-!
# Ordinary lexicographic ordering of actual projected frontier cones

The corrected Lemma 27 frontiers are sorted by the repaired
length-first ForwardAux order. That is NOT automatically the
ordinary lex order needed for skew clause II.

Two relevant orientations can nevertheless be derived from
the complete T's actual skew axioms and frontier geometry:

* Among frontiers of the SAME intrinsic T rank, coordinate
  order implies ordinary lex order of ALL projected descendants.
* Every rank-(m+1) frontier cone is lexicographically to the
  LEFT of every rank-m frontier cone. The key is its genuine
  retained predecessor at rank m, which is incomparable with
  and lex left of each rank-m outside-cut frontier.

Neither assertion uses or assumes final skewness of T'_M.
The remaining equal-final-rank length comparison will need
the local vector rank/length ordering combined with these
lex geometric facts.
-/

namespace DualTree.ForwardQFinalCrossBandLex

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut

/-- At equal original ambient frontier rank, increasing
the actual sorted frontier index also increases ordinary
lex order of EVERY pair of projected descendants. -/
theorem projected_lex_of_same_frontier_rank_index_lt
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (hij : i < j)
    (hrank :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1)
    (z w : BoundedNode b (k-(m+1))) :
    FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨j,w⟩).1 := by
  let fi := ForwardOrderedProjections.frontierAt c.T c.cut i
  let fj := ForwardOrderedProjections.frontierAt c.T c.cut j
  have hfrontAux : ForwardAux fi.1 fj.1 :=
    ForwardSortedFrontiers.frontiers_get_order c.T c.cut i j hij
  have hfrontLex : FinLexLE fi.1 fj.1 :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.T (ForwardQFinalRetainedSkewLength.ambient_condIIB c)
      fi.1 fj.1 fi.2 fj.2 hrank hfrontAux
  have hdistinct : fi.1 ≠ fj.1 := by
    intro heq
    have hind : i = j :=
      ForwardOrderedProjections.frontierAt_injective c.T c.cut
        (Subtype.ext heq)
    exact (ne_of_lt hij) hind
  have hinc :
      ¬ IsPrefix fi.1 fj.1 ∧ ¬ IsPrefix fj.1 fi.1 :=
    ForwardProjectedTerminalOrder.frontiers_incomparable
      c.T c.cut fi.1 fj.1
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut i)
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut j)
      hdistinct
  obtain ⟨taili, hpi⟩ := projected_cone c ⟨i,z⟩
  obtain ⟨tailj, hpj⟩ := projected_cone c ⟨j,w⟩
  have hlex :=
    ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      fi.1 fj.1 taili tailj hfrontLex hinc.1 hinc.2
  rw [hpi, hpj]
  exact hlex

/-- The actual rank-(m+1) frontier cone lies ORDINARY
lexicographically BEFORE every rank-m frontier cone,
independently of stretched ambient edges or local addresses.
Its rank-m retained ancestor supplies the separating
incomparable prefix. -/
theorem projected_rank_succ_lex_before_rank_m
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (hi :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (hj :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 = m + 1)
    (z w : BoundedNode b (k-(m+1))) :
    FinLexLE (projected c ⟨j,w⟩).1
      (projected c ⟨i,z⟩).1 := by
  let fi := ForwardOrderedProjections.frontierAt c.T c.cut i
  let fj := ForwardOrderedProjections.frontierAt c.T c.cut j
  have hsmaller : m < SkewTree.heightAt c.T fj.1 := by
    rw [hj]
    omega
  obtain ⟨s, hsT, hsRank, hsStrict⟩ :=
    ForwardCompleteRankPredecessor.exists_strict_predecessor_at_rank
      c.T c.hcomplete fj.1 fj.2 m hsmaller
  have hsBefore : ForwardAux s c.cut :=
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut j).2.2
      s hsT hsStrict
  have hsRet : s ∈ retained c := by
    change s ∈ c.T.toFinset.filter (fun t => ForwardAux t c.cut)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hsT, hsBefore⟩
  have hsrcLex : FinLexLE s fi.1 :=
    ForwardQFinalFrontierLex.retained_rank_m_lex_before_frontier_rank_m
      c s hsRet hsRank i hi
  have hinc :
      ¬ IsPrefix s fi.1 ∧ ¬ IsPrefix fi.1 s :=
    ForwardQFinalFrontierLex.retained_rank_m_incomparable_frontier_rank_m
      c s hsRet hsRank i hi
  have hsProjected : IsPrefix s (projected c ⟨j,w⟩).1 :=
    isPrefix_trans hsStrict.1 (projected_cone c ⟨j,w⟩)
  obtain ⟨tailj, hpj⟩ := hsProjected
  obtain ⟨taili, hpi⟩ := projected_cone c ⟨i,z⟩
  have hlex :=
    ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      s fi.1 tailj taili hsrcLex hinc.1 hinc.2
  rw [hpj, hpi]
  exact hlex

end DualTree.ForwardQFinalCrossBandLex
