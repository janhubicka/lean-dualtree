import DualTree.SignatureMarker
import DualTree.FullBeforeSignature

/-!
# Directional support extensions from full branching

In Lemma 27, the ambient successors t0++[i] belong to the marker set R.
A complete skew support must have a descendant in each direction from an
interior node t0 which occurs before the final branching witness.

This file proves the basic branch-existence implication from the executable
fullBeforeB clause, and discharges the directional existence hypothesis of
SignatureMarker under that clause. The remaining source-facing geometric
step is to show that the particular distinguished node t0 in Lemma 27
precedes the final branching witness of the full complete skew support.
-/

namespace DualTree.DirectionalSupport

/-- Every possible direction occurs in the executable enumeration. -/
theorem mem_allFin (b : Nat) (i : Fin b) :
    i ∈ SkewTree.allFin b := by
  induction b with
  | zero =>
      exact i.elim0
  | succ b ih =>
      by_cases hlast : i.val = b
      · have hi : i = Fin.last b := Fin.ext hlast
        rw [hi]
        simp [SkewTree.allFin]
      · have hlt : i.val < b := by omega
        let j : Fin b := ⟨i.val, hlt⟩
        have hcast : Fin.castSucc j = i := Fin.ext rfl
        change i ∈ (SkewTree.allFin b).map Fin.castSucc ++ [Fin.last b]
        exact List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨j, ih j, hcast⟩))

/-- The Boolean prefix test implies the paper's explicit prefix relation. -/
theorem prefix_of_isPrefixOf_true {b : Nat}
    {s t : Node b}
    (h : s.isPrefixOf t = true) : IsPrefix s t := by
  induction s generalizing t with
  | nil =>
      exact ⟨t, by simp⟩
  | cons a as ih =>
      cases t with
      | nil =>
          simp at h
      | cons c cs =>
          have hpair : a = c ∧ as.isPrefixOf cs = true := by
            simpa [List.isPrefixOf_cons_cons] using h
          rcases hpair with ⟨rfl, htail⟩
          rcases ih htail with ⟨u, hu⟩
          refine ⟨u, ?_⟩
          simp [hu]

/-- A witnessed successor in a given direction yields an ambient descendant. -/
theorem descendant_of_uniqueBranch
    {b : Nat} (T : List (Node b))
    (cut : Node b) (i : Fin b)
    (h : SkewTree.uniqueBranchB T cut i = true) :
    ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t := by
  have hlen :
      (SkewTree.branchWitnesses T cut i).length = 1 := by
    simpa [SkewTree.uniqueBranchB] using h
  cases hs : SkewTree.branchWitnesses T cut i with
  | nil =>
      simp [hs] at hlen
  | cons t rest =>
      have ht : t ∈ SkewTree.branchWitnesses T cut i := by
        simp [hs]
      change t ∈ T.filter
        (fun x => SkewTree.immediateSuccB T cut x &&
          (cut ++ [i]).isPrefixOf x) at ht
      rcases List.mem_filter.mp ht with ⟨htT, htest⟩
      have hp : (cut ++ [i]).isPrefixOf t = true := by
        simp only [Bool.and_eq_true] at htest
        exact htest.2
      exact ⟨t, htT, prefix_of_isPrefixOf_true hp⟩

/--
The fullBeforeB property at a later branching witness forces all
directions from the earlier node cut to have support descendants.
-/
theorem directional_descendants_of_fullBefore
    {b : Nat}
    (T : List (Node b))
    (aux : Node b → Node b → Bool)
    (cut witness : Node b)
    (hfull : SkewTree.fullBeforeB aux T witness = true)
    (hcut : cut ∈ T)
    (hbefore : aux cut witness = true)
    (hne : cut ≠ witness) :
    ∀ i : Fin b, ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t := by
  have hentry :
      (SkewTree.allFin b).all
        (fun i => SkewTree.uniqueBranchB T cut i) = true := by
    have h := (List.all_eq_true.mp hfull) cut hcut
    simpa [hbefore, hne] using h
  intro i
  have hbranch : SkewTree.uniqueBranchB T cut i = true :=
    (List.all_eq_true.mp hentry) i (mem_allFin b i)
  exact descendant_of_uniqueBranch T cut i hbranch

/--
Under the full-branching clause of a later support node, the two types
of signature cone markers both have support descendants.
-/
theorem coneMarker_has_descendant_of_fullBefore
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (witness : Node b)
    (hfull : SkewTree.fullBeforeB SkewTree.paperAuxB T witness = true)
    (hbefore : SkewTree.paperAuxB cut witness = true)
    (hne : cut ≠ witness)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    ∃ t, t ∈ T ∧ IsPrefix s t := by
  apply SignatureMarker.coneMarker_has_support_descendant
    O cut hout T hST
    (directional_descendants_of_fullBefore T SkewTree.paperAuxB
      cut witness hfull hcut hbefore hne)
    hs

end DualTree.DirectionalSupport
