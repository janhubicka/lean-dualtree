import DualTree.MeetClosedFromBranching

/-!
# Complete skew supports have unique directional successors

For a non-singleton complete skew support, the final branching witness
from clause (iv) must have all b immediate successors: its partial
branching parameter reaches b - 1 because completeness excludes
nonempty proper partial branching.  Thus every support node has at
most one immediate successor in each ambient direction.

The auxiliary order is parameterized.  We require only comparability
of distinct nodes in the order; this is later discharged for both the
printed and the forward-lex auxiliary order.
-/

namespace DualTree.CompleteSkewMeet

/-- Completeness forces every direction to occur uniquely at the final branching witness. -/
theorem full_directions_at_complete_witness
    {b k : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b)) (star : Node b) (iStar : Fin b)
    (hcomplete : SkewTree.completeB aux k T = true)
    (hstar : star ∈ T)
    (hpartial : SkewTree.partialAtB T star iStar = true) :
    ∀ i : Fin b, SkewTree.uniqueBranchB T star i = true := by
  have hcomp := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hcomp
  have hrow := (List.all_eq_true.mp hcomp.2) star hstar
  change
    (if (SkewTree.immediateSuccs T star).length = 0
     then decide (SkewTree.heightAt T star + 1 = k)
     else decide ((SkewTree.immediateSuccs T star).length = b)) = true
    at hrow
  have hp := hpartial
  simp only [SkewTree.partialAtB, Bool.and_eq_true] at hp
  have hcount :
      (SkewTree.immediateSuccs T star).length = iStar.val + 1 := by
    simpa using hp.1
  have hpos : (SkewTree.immediateSuccs T star).length ≠ 0 := by
    omega
  have hbranchCount : (SkewTree.immediateSuccs T star).length = b := by
    simpa [hpos] using hrow
  have hlast : iStar.val + 1 = b := by omega
  intro i
  have hle : i ≤ iStar := by
    change i.val ≤ iStar.val
    have hi := i.isLt
    omega
  have hdir : i ∈ SkewTree.dirsUpTo iStar := by
    unfold SkewTree.dirsUpTo
    exact List.mem_filter.mpr
      ⟨DirectionalSupport.mem_allFin b i, by simp [hle]⟩
  exact (List.all_eq_true.mp hp.2) i hdir

/-- No immediate support successors imply no directional branch witnesses. -/
theorem branchWitnesses_nil_of_immediateSuccs_nil
    {b : Nat} (T : List (Node b))
    (s : Node b) (i : Fin b)
    (hzero : SkewTree.immediateSuccs T s = []) :
    SkewTree.branchWitnesses T s i = [] := by
  unfold SkewTree.branchWitnesses
  exact StarredSignature.filter_conj_eq_nil T
    (fun u => SkewTree.immediateSuccB T s u)
    (fun u => (s ++ [i]).isPrefixOf u)
    (by simpa [SkewTree.immediateSuccs] using hzero)

/-- Clause (iv) is present in every nonsingleton skew support. -/
theorem condIVB_of_skew_nonSingleton
    {b : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hskew : SkewTree.skewB aux T = true)
    (hnonsingleton : T.length ≠ 1) :
    SkewTree.condIVB aux T = true := by
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have h := hparts.2
  simp [hnonsingleton, Bool.and_eq_true] at h
  exact h.2

/-- Clause (i) supplies a common support root for any pair of support nodes. -/
theorem rootedB_of_skew_nonSingleton
    {b : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hskew : SkewTree.skewB aux T = true)
    (hnonsingleton : T.length ≠ 1) :
    SkewTree.rootedB T = true := by
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have h := hparts.2
  simp [hnonsingleton, Bool.and_eq_true] at h
  exact h.1.1.1

/--
The complete-skew conditions imply uniqueness of immediate support
successors in every direction, for any auxiliary order which compares
every pair of distinct nodes.
-/
theorem atMostOneDirection_of_complete_total
    {b k : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB aux k T = true)
    (hnonsingleton : T.length ≠ 1)
    (htotal : ∀ s t : Node b, s ≠ t →
      aux s t = true ∨ aux t s = true) :
    MeetClosedFromBranching.AtMostOneDirection T := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hIV : SkewTree.condIVB aux T = true :=
    condIVB_of_skew_nonSingleton aux T hparts.1 hnonsingleton
  unfold SkewTree.condIVB at hIV
  rcases List.any_eq_true.mp hIV with ⟨star, hstar, hany⟩
  rcases List.any_eq_true.mp hany with ⟨iStar, hiStar, hbranches⟩
  have hfull : SkewTree.fullBeforeB aux T star = true := by
    have h := hbranches
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hempty : SkewTree.emptyAfterB aux T star = true := by
    have h := hbranches
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  have hpartial : SkewTree.partialAtB T star iStar = true := by
    have h := hbranches
    simp only [Bool.and_eq_true] at h
    exact h.2
  have hstarFull : ∀ i : Fin b,
      SkewTree.uniqueBranchB T star i = true :=
    full_directions_at_complete_witness aux T star iStar
      hcomplete hstar hpartial
  intro s hs i x y hx hy
  by_cases heq : s = star
  · subst s
    exact SkewBranchGeometry.eq_of_mem_uniqueBranch T star i
      (hstarFull i) hx hy
  · rcases htotal s star heq with hbefore | hafter
    · have hentry :
          (SkewTree.allFin b).all
            (fun j => SkewTree.uniqueBranchB T s j) = true := by
        have h := (List.all_eq_true.mp hfull) s hs
        simpa [hbefore, heq] using h
      have huniq : SkewTree.uniqueBranchB T s i = true :=
        (List.all_eq_true.mp hentry) i
          (DirectionalSupport.mem_allFin b i)
      exact SkewBranchGeometry.eq_of_mem_uniqueBranch T s i
        huniq hx hy
    · have hzeroBool : (SkewTree.immediateSuccs T s).isEmpty = true := by
        have h := (List.all_eq_true.mp hempty) s hs
        simpa [hafter, heq] using h
      have hzero : SkewTree.immediateSuccs T s = [] := by
        cases hh : SkewTree.immediateSuccs T s with
        | nil => rfl
        | cons u us => simp [hh] at hzeroBool
      have hbranchZero :=
        branchWitnesses_nil_of_immediateSuccs_nil T s i hzero
      rw [hbranchZero] at hx
      cases hx

/-- A nonsingleton complete skew support is ambient meet-closed. -/
theorem meetClosed_of_complete_total
    {b k : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB aux k T = true)
    (hnonsingleton : T.length ≠ 1)
    (htotal : ∀ s t : Node b, s ≠ t →
      aux s t = true ∨ aux t s = true) :
    MeetGeometry.MeetClosed T := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  exact MeetClosedFromBranching.meetClosed_of_rooted_uniqueDirections
    T
    (rootedB_of_skew_nonSingleton aux T hc.1 hnonsingleton)
    (atMostOneDirection_of_complete_total aux T
      hcomplete hnonsingleton htotal)

end DualTree.CompleteSkewMeet
