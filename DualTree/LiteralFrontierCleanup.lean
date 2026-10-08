import DualTree.SignatureInteriorPersistence

/-!
# Remove redundant hypotheses in the literal-R frontier geometry

A cut strictly below the final intrinsic level of a complete skew
tree cannot occur in a singleton support. Thus the separate
nonsingleton parameter in earlier frontier lemmas is unnecessary.

Moreover, if the ambient support T lies inside b^{<N}, the existence
of descendants in every direction at such a cut shows that all
ambient children cut++[i] are themselves in b^{<N}. This justifies
using the full direction list for the second term of the printed R.
-/

namespace DualTree.LiteralFrontierCleanup

/-- An early interior level forces the complete support to be nonsingleton. -/
theorem nonsingleton_of_early_level
    {b k : Nat} (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    T.length ≠ 1 := by
  have hnonleaf :=
    CompleteInteriorBranching.nonleaf_of_height_lt
      SkewTree.paperAuxB T hcomplete cut hcut hlevel
  intro hlen
  cases hT : T with
  | nil =>
      simp [hT] at hlen
  | cons root rest =>
      cases rest with
      | nil =>
          have hroot : cut = root := by simpa [hT] using hcut
          subst cut
          have hzero :
              (SkewTree.immediateSuccs [root] root).length = 0 := by
            simp [SkewTree.immediateSuccs,
              SkewTree.immediateSuccB, SkewTree.strictPrefixB]
          exact hnonleaf (by simpa [hT] using hzero)
      | cons u us =>
          simp [hT] at hlen

/-- Candidate-marker frontiers need no separate nonsingleton assumption. -/
theorem coneMarker_unique_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f :=
  CompleteInteriorBranching.coneMarker_unique_frontier_of_complete_height
    O cut hout T hcomplete
    (nonsingleton_of_early_level T hcomplete cut hcut hlevel)
    hST hcut hlevel hs

/-- The literal R correspondence at a maximal interior cut, without nonsingleton. -/
theorem literalR_unique_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ LiteralSignatureR.literalR O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f :=
  SignatureInteriorPersistence.literalR_unique_frontier_of_maxInterior
    O cut hcut hmax hout T hcomplete
    (nonsingleton_of_early_level T hcomplete cut hcutT hlevel)
    hST hcutT hlevel hs

/-- A prefix of an ambient-bounded support point is itself ambient-bounded. -/
theorem child_bounded_of_support_descendant {b N : Nat}
    (T : List (Node b))
    (hbounded : ∀ t, t ∈ T → InHomTree N t)
    (cut : Node b) (i : Fin b)
    (hdesc : ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t) :
    InHomTree N (cut ++ [i]) := by
  rcases hdesc with ⟨t, ht, hp⟩
  exact lt_of_le_of_lt (prefix_length_le hp) (hbounded t ht)

/--
All immediate ambient children of an early cut are in the ambient tree:
full directional branching supplies a bounded support descendant.
-/
theorem all_children_bounded_of_early_level
    {b k N : Nat} (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hbounded : ∀ t, t ∈ T → InHomTree N t)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    ∀ i : Fin b, InHomTree N (cut ++ [i]) := by
  have hnon := nonsingleton_of_early_level T hcomplete
    cut hcut hlevel
  intro i
  have hbranch : SkewTree.uniqueBranchB T cut i = true :=
    CompleteInteriorBranching.fullDirections_of_height_lt_paper
      T hcomplete hnon cut hcut hlevel i
  exact child_bounded_of_support_descendant T hbounded cut i
    (DirectionalSupport.descendant_of_uniqueBranch T cut i hbranch)

end DualTree.LiteralFrontierCleanup
