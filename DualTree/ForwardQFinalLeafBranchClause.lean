import DualTree.ForwardQFinalExactBranching
import DualTree.ForwardQFinalRankBound
import DualTree.ImmediateSupportHeight

/-!
# The full numerical completeness (leaf-or-b-branching) clause of final T'

For the exact target-M=m+q support T'_M, prior proofs establish:
* every final-support vertex has genuine intrinsic rank < M
  when q>0 (the cut rank m is then strictly below M);
* each vertex of rank r with r+1<M has exactly one
  immediate SUPPORT successor in each of b directions,
  hence precisely b immediate successors in total.

Any final-support vertex at rank M-1 must be a LEAF:
an immediate successor would have intrinsic rank M by
the generic immediate-support rank formula, contradicting
the checked bound that every final vertex has rank <M.

If b>0 and q>0, the converse holds: any early vertex has
exactly b>0 successors and therefore is NOT a leaf.
Combining both cases yields the entire Boolean branching
clause of completeB for the assembled final support.

Thus, conditional only on the independent remaining global
skewB assertion, T'_M is already M-complete. In particular,
this module reduces the remaining M-complete skew theorem
to proving the genuine global skew order/meet geometry.
The final ambient word f' and the Ramsey induction are not
claimed here.
-/

namespace DualTree.ForwardQFinalLeafBranchClause

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalExactBranching

/-- An actual vertex of final intrinsic rank M-1
has NO immediate support successor. This is forced by
the exact ALL-vertex rank bound and the strict rank
increase at every immediate support edge, not by
assuming final support completeness. -/
theorem final_last_level_is_leaf
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hq : 0 < q)
    (s : Node b)
    (hs : s ∈ finalBudgetSupport c f (m+q))
    (hlast :
      SkewTree.heightAt
        (finalBudgetSupport c f (m+q)).toList s + 1 = m+q) :
    (SkewTree.immediateSuccs
      (finalBudgetSupport c f (m+q)).toList s).length = 0 := by
  classical
  let S := (finalBudgetSupport c f (m+q)).toList
  cases hlist : SkewTree.immediateSuccs S s with
  | nil =>
      simp [hlist]
  | cons t rest =>
      have htSucc : t ∈ SkewTree.immediateSuccs S s := by
        simp [hlist]
      have htFiltered :
          t ∈ S.filter (fun u => SkewTree.immediateSuccB S s u) :=
        htSucc
      obtain ⟨htMember,hstep⟩ := List.mem_filter.mp htFiltered
      have hrank : SkewTree.heightAt S t =
          SkewTree.heightAt S s + 1 :=
        ImmediateSupportHeight.heightAt_immediate
          S s t
          (Finset.nodup_toList (finalBudgetSupport c f (m+q)))
          (Finset.mem_toList.mpr hs) hstep
      have htarget : SkewTree.heightAt S t < m+q :=
        ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
          c f (m+q) (by omega) t
            (Finset.mem_toList.mp htMember)
      omega

/-- The entire COMPUTABLE complete-branching condition
is now checked for final T'_(m+q), provided b and q are
positive. The case b=0 is genuinely degenerate: a
zero-ary complete tree can have no nonempty directional
successor even below the last level. -/
theorem final_complete_branch_clause
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hb : 0 < b)
    (hq : 0 < q) :
    (finalBudgetSupport c f (m+q)).toList.all
      (fun s =>
        if (SkewTree.immediateSuccs
            (finalBudgetSupport c f (m+q)).toList s).length = 0
        then decide (
          SkewTree.heightAt
            (finalBudgetSupport c f (m+q)).toList s + 1 = m+q)
        else decide (
          (SkewTree.immediateSuccs
            (finalBudgetSupport c f (m+q)).toList s).length = b)) =
    true := by
  classical
  let S := (finalBudgetSupport c f (m+q)).toList
  apply List.all_eq_true.mpr
  intro s hsS
  have hs : s ∈ finalBudgetSupport c f (m+q) :=
    Finset.mem_toList.mp hsS
  have hlt :
      SkewTree.heightAt S s < m+q :=
    ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
      c f (m+q) (by omega) s hs
  by_cases hroom : SkewTree.heightAt S s + 1 < m+q
  · have hcount :
        (SkewTree.immediateSuccs S s).length = b :=
      final_immediateSuccs_length_eq_b_below_last
        c f s hs hroom
    have hnonzero :
        (SkewTree.immediateSuccs S s).length ≠ 0 := by
      omega
    change
      (if (SkewTree.immediateSuccs S s).length = 0
       then decide (SkewTree.heightAt S s + 1 = m+q)
       else decide ((SkewTree.immediateSuccs S s).length = b)) = true
    simp [hnonzero,hcount]
  · have hlast : SkewTree.heightAt S s + 1 = m+q := by
      omega
    have hzero : (SkewTree.immediateSuccs S s).length = 0 :=
      final_last_level_is_leaf c f hq s hs hlast
    change
      (if (SkewTree.immediateSuccs S s).length = 0
       then decide (SkewTree.heightAt S s + 1 = m+q)
       else decide ((SkewTree.immediateSuccs S s).length = b)) = true
    simp [hzero,hlast]

/-- Under b,q>0, the last remaining condition for the
M-completeness of the genuine rank-filtered final T'
is exactly the skewB condition in the repaired forward
auxiliary order. The full branching and leaf test has
been discharged, but the skewB condition remains open. -/
theorem final_complete_iff_skew
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hb : 0 < b)
    (hq : 0 < q) :
    SkewTree.completeB SkewTree.forwardAuxB (m+q)
      (finalBudgetSupport c f (m+q)).toList = true ↔
    SkewTree.skewB SkewTree.forwardAuxB
      (finalBudgetSupport c f (m+q)).toList = true := by
  unfold SkewTree.completeB
  simp only [Bool.and_eq_true]
  exact ⟨And.left,fun hs =>
    ⟨hs,final_complete_branch_clause c f hb hq⟩⟩

end DualTree.ForwardQFinalLeafBranchClause
