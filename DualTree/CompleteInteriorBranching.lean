import DualTree.InclusiveSignatureMarkers

/-!
# Full directional branching strictly below the last complete level

The complete-skew axioms imply that no node below the last intrinsic
level can be a leaf. Clause (iv) then makes every such node fully
branching, without identifying the exact intrinsic height of the
last branching witness. This removes the outstanding witness-height
assumption from the candidate-marker/frontier construction of Lemma 27.

As before, the literal equality of the candidate marker list with the
paper's R and the subsequent variable-word coding are separate tasks.
-/

namespace DualTree.CompleteInteriorBranching

/-- A complete skew support cannot have a leaf at an earlier intrinsic level. -/
theorem nonleaf_of_height_lt {b k : Nat}
    (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB aux k T = true)
    (s : Node b) (hs : s ∈ T)
    (hlevel : SkewTree.heightAt T s + 1 < k) :
    (SkewTree.immediateSuccs T s).length ≠ 0 := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hrow := (List.all_eq_true.mp hparts.2) s hs
  change
    (if (SkewTree.immediateSuccs T s).length = 0
     then decide (SkewTree.heightAt T s + 1 = k)
     else decide ((SkewTree.immediateSuccs T s).length = b)) = true
    at hrow
  intro hzero
  have heq : SkewTree.heightAt T s + 1 = k := by
    simpa [hzero] using hrow
  omega

/--
Every actual non-leaf in a nonsingleton complete skew support has
exactly one immediate support successor in every ambient direction.
The auxiliary order is required only to compare distinct nodes.
-/
theorem fullDirections_of_complete_nonleaf_total
    {b k : Nat} (aux : Node b → Node b → Bool)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB aux k T = true)
    (hnonsingleton : T.length ≠ 1)
    (htotal : ∀ s t : Node b, s ≠ t →
      aux s t = true ∨ aux t s = true)
    (s : Node b) (hs : s ∈ T)
    (hnonleaf : (SkewTree.immediateSuccs T s).length ≠ 0) :
    ∀ i : Fin b, SkewTree.uniqueBranchB T s i = true := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hIV : SkewTree.condIVB aux T = true :=
    CompleteSkewMeet.condIVB_of_skew_nonSingleton
      aux T hparts.1 hnonsingleton
  unfold SkewTree.condIVB at hIV
  rcases List.any_eq_true.mp hIV with ⟨star, hstar, hstarAny⟩
  rcases List.any_eq_true.mp hstarAny with
    ⟨iStar, _hiStar, hbranches⟩
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
    CompleteSkewMeet.full_directions_at_complete_witness
      aux T star iStar hcomplete hstar hpartial
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
        cases hlist : SkewTree.immediateSuccs T s with
        | nil => rfl
        | cons u us => simp [hlist] at hzeroBool
      exact (hnonleaf hzero).elim

/-- Every level below the last one is fully branching under the printed order. -/
theorem fullDirections_of_height_lt_paper {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (s : Node b) (hs : s ∈ T)
    (hlevel : SkewTree.heightAt T s + 1 < k) :
    ∀ i : Fin b, SkewTree.uniqueBranchB T s i = true :=
  fullDirections_of_complete_nonleaf_total SkewTree.paperAuxB T
    hcomplete hnonsingleton
    (fun s t _ => SkewMeetInstantiation.paperAuxB_total s t)
    s hs (nonleaf_of_height_lt SkewTree.paperAuxB T
      hcomplete s hs hlevel)

/-- All candidate signature cone markers have support descendants at early cuts. -/
theorem coneMarker_descendant_of_height_lt
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    ∃ t, t ∈ T ∧ IsPrefix s t := by
  have hbranches : ∀ i : Fin b,
      ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t := by
    intro i
    exact DirectionalSupport.descendant_of_uniqueBranch
      T cut i
      (fullDirections_of_height_lt_paper T hcomplete
        hnonsingleton cut hcut hlevel i)
  exact SignatureMarker.coneMarker_has_support_descendant
    O cut hout T hST hbranches hs

/--
The source's inclusive-cut frontier geometry for all candidate markers,
with no separate branching witness or witness-height formula.
-/
theorem coneMarker_unique_frontier_of_complete_height
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f := by
  exact InclusiveFrontier.unique_frontier_complete_paper
    T hcomplete cut s
    (InclusiveSignatureMarkers.coneMarker_paperCutBoundary
      O cut hout hs)
    (coneMarker_descendant_of_height_lt
      O cut hout T hcomplete hnonsingleton hST
      hcut hlevel hs)

end DualTree.CompleteInteriorBranching
