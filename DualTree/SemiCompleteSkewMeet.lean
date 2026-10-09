import DualTree.SkewMeetInstantiation

/-!
# Ambient meet closure of semi-complete skew supports

The previous development established meet closure for complete skew
supports. The signature skeleton from Definition 26, however, comes
from a *semi-complete* skew tree, whose leaves need not all have
the same intrinsic height.

This module proves that completeness of leaf levels is unnecessary.
Clause (iv) of skewness selects the final branching witness.
Semi-completeness forces its nonzero number of immediate successors
to equal b, so its partial branching parameter reaches b-1.
The other non-leaves lie before the witness and have all directions,
while later vertices are leaves.

Thus every semi-complete skew support has at most one immediate
successor in each direction and, by rootedness, is closed under
ambient longest-common-prefix meets. In fact, all its non-leaves
have *exactly one* successor in each direction.

The result is used as a source-side ingredient of the remaining
Lemma 27 semi-completeness proof for S_w.
-/

namespace DualTree.SemiCompleteSkewMeet

/-- Semi-completeness forces all directions to occur at the
final branching witness of a nonsingleton skew tree. -/
theorem full_directions_at_witness
    {b : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b)) (star : Node b) (iStar : Fin b)
    (hsemi : SkewTree.semiCompleteB aux T = true)
    (hstar : star ∈ T)
    (hpartial : SkewTree.partialAtB T star iStar = true) :
    ∀ i : Fin b, SkewTree.uniqueBranchB T star i = true := by
  have hsc := hsemi
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsc
  have hrow := (List.all_eq_true.mp hsc.2) star hstar
  change decide
    ((SkewTree.immediateSuccs T star).length = 0 ∨
      (SkewTree.immediateSuccs T star).length = b) = true at hrow
  have hp := hpartial
  simp only [SkewTree.partialAtB, Bool.and_eq_true] at hp
  have hcount :
      (SkewTree.immediateSuccs T star).length = iStar.val + 1 := by
    simpa using hp.1
  have hnonzero : (SkewTree.immediateSuccs T star).length ≠ 0 := by
    omega
  have hsize : (SkewTree.immediateSuccs T star).length = b := by
    have hcases :
        (SkewTree.immediateSuccs T star).length = 0 ∨
          (SkewTree.immediateSuccs T star).length = b := by
      simpa using hrow
    exact hcases.resolve_left hnonzero
  have hlast : iStar.val + 1 = b := by omega
  intro i
  have hle : i ≤ iStar := by
    change i.val ≤ iStar.val
    have hib := i.isLt
    omega
  have hdir : i ∈ SkewTree.dirsUpTo iStar := by
    unfold SkewTree.dirsUpTo
    exact List.mem_filter.mpr
      ⟨DirectionalSupport.mem_allFin b i, by simp [hle]⟩
  exact (List.all_eq_true.mp hp.2) i hdir

/-- Every node of a semi-complete skew support has at most one
immediate successor in each ambient direction. -/
theorem atMostOneDirection_of_semiComplete_total
    {b : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hsemi : SkewTree.semiCompleteB aux T = true)
    (hnonsingleton : T.length ≠ 1)
    (htotal : ∀ s t : Node b, s ≠ t →
      aux s t = true ∨ aux t s = true) :
    MeetClosedFromBranching.AtMostOneDirection T := by
  have hparts := hsemi
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hIV : SkewTree.condIVB aux T = true :=
    CompleteSkewMeet.condIVB_of_skew_nonSingleton
      aux T hparts.1 hnonsingleton
  unfold SkewTree.condIVB at hIV
  rcases List.any_eq_true.mp hIV with ⟨star, hstar, hany⟩
  rcases List.any_eq_true.mp hany with ⟨iStar, _hiStar, hbranches⟩
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
    full_directions_at_witness aux T star iStar hsemi hstar hpartial
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
    · have hzeroBool :
          (SkewTree.immediateSuccs T s).isEmpty = true := by
        have h := (List.all_eq_true.mp hempty) s hs
        simpa [hafter, heq] using h
      have hzero : SkewTree.immediateSuccs T s = [] := by
        cases hh : SkewTree.immediateSuccs T s with
        | nil => rfl
        | cons u us => simp [hh] at hzeroBool
      have hbranchZero :=
        CompleteSkewMeet.branchWitnesses_nil_of_immediateSuccs_nil
          T s i hzero
      rw [hbranchZero] at hx
      cases hx

/-- Every non-leaf of a nonsingleton semi-complete skew tree
has exactly one immediate successor in each direction. -/
theorem fullDirections_of_semiComplete_nonleaf_total
    {b : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hsemi : SkewTree.semiCompleteB aux T = true)
    (hnonsingleton : T.length ≠ 1)
    (htotal : ∀ s t : Node b, s ≠ t →
      aux s t = true ∨ aux t s = true)
    (s : Node b) (hs : s ∈ T)
    (hnonleaf : (SkewTree.immediateSuccs T s).length ≠ 0) :
    ∀ i : Fin b, SkewTree.uniqueBranchB T s i = true := by
  have hparts := hsemi
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hIV : SkewTree.condIVB aux T = true :=
    CompleteSkewMeet.condIVB_of_skew_nonSingleton
      aux T hparts.1 hnonsingleton
  unfold SkewTree.condIVB at hIV
  rcases List.any_eq_true.mp hIV with ⟨star, hstar, hany⟩
  rcases List.any_eq_true.mp hany with ⟨iStar, _hiStar, hbranches⟩
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
    full_directions_at_witness aux T star iStar hsemi hstar hpartial
  intro i
  by_cases heq : s = star
  · subst s
    exact hstarFull i
  · rcases htotal s star heq with hbefore | hafter
    · have hentry :
          (SkewTree.allFin b).all
            (fun j => SkewTree.uniqueBranchB T s j) = true := by
        have h := (List.all_eq_true.mp hfull) s hs
        simpa [hbefore, heq] using h
      exact (List.all_eq_true.mp hentry) i
        (DirectionalSupport.mem_allFin b i)
    · have hzeroBool :
          (SkewTree.immediateSuccs T s).isEmpty = true := by
        have h := (List.all_eq_true.mp hempty) s hs
        simpa [hafter, heq] using h
      have hzero : (SkewTree.immediateSuccs T s).length = 0 := by
        cases hh : SkewTree.immediateSuccs T s with
        | nil => rfl
        | cons u us => simp [hh] at hzeroBool
      exact (hnonleaf hzero).elim

/-- Every semi-complete skew support under the printed auxiliary
order is closed under ambient longest-common-prefix meets. -/
theorem meetClosed_semiComplete_paper {b : Nat}
    (T : List (Node b))
    (hsemi : SkewTree.semiCompleteB SkewTree.paperAuxB T = true) :
    MeetGeometry.MeetClosed T := by
  by_cases hsingle : T.length = 1
  · exact SkewMeetInstantiation.meetClosed_length_one T hsingle
  · have hc := hsemi
    simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hc
    exact MeetClosedFromBranching.meetClosed_of_rooted_uniqueDirections
      T (CompleteSkewMeet.rootedB_of_skew_nonSingleton
        SkewTree.paperAuxB T hc.1 hsingle)
      (atMostOneDirection_of_semiComplete_total
        SkewTree.paperAuxB T hsemi hsingle
        (fun s t _ => SkewMeetInstantiation.paperAuxB_total s t))

/-- For a starred word the support is semi-complete by definition,
so its ambient meet-closure requires no extra assumption. -/
theorem meetClosed_starred
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b))) :
    MeetGeometry.MeetClosed O.tree :=
  meetClosed_semiComplete_paper O.tree O.semi_complete

end DualTree.SemiCompleteSkewMeet
