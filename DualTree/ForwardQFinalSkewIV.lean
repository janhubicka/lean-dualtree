import DualTree.ForwardAuxFiniteMaximum
import DualTree.ForwardQFinalLeafBranchClause
import DualTree.ForwardQFinalSkewIII
import DualTree.ForwardQFinalMeetClosure
import DualTree.LastBranchWitness

/-!
# The final branching witness (skew clause IV) of the corrected Lemma 27

For b>0, q>0 and final target height M=m+q>1, the exact
rank-filtered final support S has the following independently
verified properties:
* its unique ambient T root remains in S;
* every S vertex has intrinsic height < M;
* vertices below last intrinsic rank have exactly one immediate
  successor in each of b directions;
* all last-rank vertices are terminal;
* skew clause III already strictly separates lengths of
  earlier intrinsic ranks from later ranks.

Thus S has an interior vertex, and a maximal one in the
corrected forward auxiliary order. Call it star.

Any S vertex strictly AFTER star must be terminal, by
maximality of star among interior vertices. Any vertex
strictly BEFORE star must lie below the final intrinsic
level, because skew clause III would otherwise force
its ambient length to EXCEED star's length. Therefore
all such earlier vertices have every direction uniquely
represented. Finally star itself has all b directions,
so the generic full-last-witness lemma supplies clause IV
with maximal direction b-1.

This is a genuine condIVB theorem on the actual final support,
not an added hypothesis or a claim about the printed starred
mixed-product ordering. The degenerate target height M=1
is deliberately treated separately by the singleton-skew
convention when proving the global final skewB theorem.
-/

namespace DualTree.ForwardQFinalSkewIV

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalExactBranching

/-- For positive b and q and nontrivial final height m+q>1,
the ACTUAL rank-filtered final support possesses the final
forward-auxiliary branching witness required by skew clause IV.
No full skewB or completeB assumption on S is used. -/
theorem finalBudgetSupport_condIVB
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hb : 0 < b) (hq : 0 < q)
    (hM : 1 < m+q) :
    SkewTree.condIVB SkewTree.forwardAuxB
      (finalBudgetSupport c f (m+q)).toList = true := by
  classical
  let S := (finalBudgetSupport c f (m+q)).toList
  let r := ForwardCompleteEmbedding.rootOf c.T c.hcomplete c.hnon
  have hrS : r ∈ S :=
    ForwardQFinalMeetClosure.ambient_root_mem_final c f
  have hrankZero : SkewTree.heightAt S r = 0 :=
    ImmediateSupportHeight.heightAt_root_zero S r
      (fun t ht =>
        ForwardQFinalMeetClosure.ambient_root_prefix_final c f t ht)
  have hrRoom : SkewTree.heightAt S r + 1 < m+q := by
    omega
  have hrCount : (SkewTree.immediateSuccs S r).length = b :=
    ForwardQFinalExactBranching.final_immediateSuccs_length_eq_b_below_last
      c f r (Finset.mem_toList.mp hrS) hrRoom
  have hrInterior : r ∈ SkewTree.interior S := by
    unfold SkewTree.interior
    apply List.mem_filter.mpr
    refine ⟨hrS, ?_⟩
    cases hrSucc : SkewTree.immediateSuccs S r with
    | nil =>
        simp [hrSucc] at hrCount
        omega
    | cons t ts =>
        simp [hrSucc]
  have hinterNonempty : SkewTree.interior S ≠ [] := by
    intro hnil
    rw [hnil] at hrInterior
    simp at hrInterior
  obtain ⟨star,hstarInterior,hmax⟩ :=
    ForwardAuxFiniteMaximum.exists_maximal
      (SkewTree.interior S) hinterNonempty
  have hstarS : star ∈ S :=
    (List.mem_filter.mp hstarInterior).1
  have hstarSuccNonempty : SkewTree.immediateSuccs S star ≠ [] := by
    intro hnil
    have hflag := (List.mem_filter.mp hstarInterior).2
    simp [hnil] at hflag
  have hstarSuccPos : 0 < (SkewTree.immediateSuccs S star).length := by
    cases hsucc : SkewTree.immediateSuccs S star with
    | nil =>
        exact False.elim (hstarSuccNonempty hsucc)
    | cons t ts =>
        simp [hsucc]
  have hstarRankBound : SkewTree.heightAt S star < m+q :=
    ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
      c f (m+q) (by omega) star (Finset.mem_toList.mp hstarS)
  have hstarRoom : SkewTree.heightAt S star + 1 < m+q := by
    by_contra hnot
    have hlast : SkewTree.heightAt S star + 1 = m+q := by
      omega
    have hzero :
        (SkewTree.immediateSuccs S star).length = 0 :=
      ForwardQFinalLeafBranchClause.final_last_level_is_leaf
        c f hq star (Finset.mem_toList.mp hstarS) hlast
    omega
  have hIII : SkewTree.condIIIB S = true :=
    ForwardQFinalSkewIII.finalBudgetSupport_condIIIB c f
  have hfullBefore :
      SkewTree.fullBeforeB SkewTree.forwardAuxB S star = true := by
    unfold SkewTree.fullBeforeB
    apply List.all_eq_true.mpr
    intro s hs
    change
      (if SkewTree.forwardAuxB s star && !(s == star)
       then (SkewTree.allFin b).all (fun dir =>
         SkewTree.uniqueBranchB S s dir)
       else true) = true
    split_ifs with hcase
    · have hh := hcase
      simp only [Bool.and_eq_true] at hh
      have hbefore : ForwardAux s star := by
        simpa [SkewTree.forwardAuxB] using hh.1
      have hbound : SkewTree.heightAt S s < m+q :=
        ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
          c f (m+q) (by omega) s (Finset.mem_toList.mp hs)
      have hroom : SkewTree.heightAt S s + 1 < m+q := by
        by_contra hnot
        have hlast : SkewTree.heightAt S s + 1 = m+q := by
          omega
        have hRankGap :
            SkewTree.heightAt S star < SkewTree.heightAt S s := by
          omega
        have hrow := (List.all_eq_true.mp hIII) star hstarS
        have hcell := (List.all_eq_true.mp hrow) s hs
        have hlen : star.length < s.length := by
          simpa [hRankGap] using hcell
        rcases hbefore with hbeforeLen | ⟨hEqLen, _⟩
        · omega
        · omega
      apply List.all_eq_true.mpr
      intro dir hdir
      exact final_uniqueBranchB_below_last_level c f s
        (Finset.mem_toList.mp hs) hroom dir
    · rfl
  have hemptyAfter :
      SkewTree.emptyAfterB SkewTree.forwardAuxB S star = true := by
    unfold SkewTree.emptyAfterB
    apply List.all_eq_true.mpr
    intro s hs
    change
      (if SkewTree.forwardAuxB star s && !(s == star)
       then (SkewTree.immediateSuccs S s).isEmpty
       else true) = true
    split_ifs with hcase
    · have hh := hcase
      simp only [Bool.and_eq_true] at hh
      have hafter : ForwardAux star s := by
        simpa [SkewTree.forwardAuxB] using hh.1
      have hne : s ≠ star := by
        intro heq
        subst s
        simp at hcase
      by_cases hterminal : (SkewTree.immediateSuccs S s).isEmpty = true
      · exact hterminal
      · have hsInterior : s ∈ SkewTree.interior S := by
          unfold SkewTree.interior
          apply List.mem_filter.mpr
          refine ⟨hs, ?_⟩
          cases hsucc : SkewTree.immediateSuccs S s with
          | nil =>
              simp [hsucc] at hterminal
          | cons t ts =>
              simp [hsucc]
        have hbefore : ForwardAux s star := hmax s hsInterior
        have heq : star = s :=
          CanonicalForwardAuxIso.forwardAux_antisymm hafter hbefore
        exact False.elim (hne heq.symm)
    · rfl
  have hcount :
      (SkewTree.immediateSuccs S star).length = b :=
    final_immediateSuccs_length_eq_b_below_last
      c f star (Finset.mem_toList.mp hstarS) hstarRoom
  have hfullCut :
      ∀ dir : Fin b, SkewTree.uniqueBranchB S star dir = true :=
    fun dir => final_uniqueBranchB_below_last_level
      c f star (Finset.mem_toList.mp hstarS) hstarRoom dir
  exact LastBranchWitness.condIVB_of_full_last_witness
    hb SkewTree.forwardAuxB S star
    hstarS hfullBefore hemptyAfter hcount hfullCut

end DualTree.ForwardQFinalSkewIV
