import DualTree.ForwardInclusiveFrontier
import DualTree.CompleteInteriorBranching

/-!
# Unique inclusive frontiers for corrected signature marker types

The repaired forward signature R comprises two kinds of markers:
(1) the first boundary of each exceptional source leaf, and
(2) the b ambient immediate children of the retained final cut.

The previous module proves unique support-frontier assignment for
*any* marker which lies on the inclusive boundary and has a
descendant in a complete forward skew support T.

Here we discharge those two requirements for both candidate
marker types, using only the forward source signature definition,
source support inclusion S⊆T, and complete forward branching of
T below its final level.

This verifies source-facing frontier existence/uniqueness for
every actual component of the forward literal R. It does not
yet identify duplicate markers or prove that *different*
members of R receive *different* frontiers; that collision-free
D₂ coordinate argument remains separate.
-/

namespace DualTree.ForwardMarkerFrontierCoverage

open ForwardSignatureBoundary

/-- The first strict-forward-cut boundary of an exceptional
leaf lies outside the inclusive forward cut, with every
strict ambient predecessor at or before that cut. -/
theorem exceptional_boundary_is_inclusive
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves O cut) :
    ForwardInclusiveFrontier.ForwardCutBoundary cut
      (firstBoundary cut t (hout t ht)) := by
  let s := firstBoundary cut t (hout t ht)
  have hb : Boundary cut t s :=
    firstBoundary_spec cut t (hout t ht)
  have hnotCut : s ≠ cut := by
    intro heq
    have hcutPrefix : IsPrefix cut t := by
      rw [← heq]
      exact hb.1
    exact (StarredSignature.exceptionalLeaves_spec
      O cut t ht).2.2 hcutPrefix
  refine ⟨?_, ?_⟩
  · intro hbefore
    exact hb.2.1 ⟨hbefore, hnotCut⟩
  · intro r hr
    exact (hb.2.2 r hr).1

/-- Every corrected exceptional-leaf signature boundary
is assigned a unique minimal outside-cut frontier in
an ambient complete forward skew support containing S. -/
theorem exceptional_boundary_unique_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves O cut) :
    ∃! f : Node b,
      CutFrontier.Frontier T
        (fun u => ForwardAux u cut) f ∧
      IsPrefix (firstBoundary cut t (hout t ht)) f := by
  have hboundary :=
    exceptional_boundary_is_inclusive O cut hout t ht
  have hleaf := (StarredSignature.exceptionalLeaves_spec O cut t ht).1
  have hdesc :
      ∃ u, u ∈ T ∧
        IsPrefix (firstBoundary cut t (hout t ht)) u :=
    ⟨t, hST t hleaf, (firstBoundary_spec cut t (hout t ht)).1⟩
  exact ForwardInclusiveFrontier.unique_frontier_complete_forward
    T hcomplete hnonsingleton cut
    (firstBoundary cut t (hout t ht)) hboundary hdesc

/-- An ambient child of the cut belongs to the boundary of
the *inclusive* forward auxiliary initial segment. -/
theorem cut_child_is_inclusive_boundary
    {b : Nat} (cut : Node b) (i : Fin b) :
    ForwardInclusiveFrontier.ForwardCutBoundary
      cut (cut ++ [i]) := by
  constructor
  · intro haux
    rcases haux with hlt | ⟨hlen, _⟩
    · simp only [List.length_append, List.length_singleton] at hlt
      omega
    · simp only [List.length_append, List.length_singleton] at hlen
      omega
  · intro r hr
    have hlen : r.length ≤ cut.length := by
      have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hr
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    have hpre : IsPrefix r cut :=
      CutFrontier.prefix_of_prefix_length_le
        hr.1 ⟨[i], rfl⟩ hlen
    by_cases hrcut : r = cut
    · subst r
      exact CanonicalForwardAuxIso.forwardAux_refl cut
    · have hstrict : IsStrictPrefix r cut := ⟨hpre, hrcut⟩
      have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hstrict
      exact Or.inl hlt

/-- Any early node of a forward k-complete support has a
descendant in every one of its b ambient directions. -/
theorem cut_child_has_support_descendant
    {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (i : Fin b) :
    ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t := by
  have htotal :
      ∀ s t : Node b, s ≠ t →
        SkewTree.forwardAuxB s t = true ∨
        SkewTree.forwardAuxB t s = true := by
    intro s t _
    rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  have hbranch : SkewTree.uniqueBranchB T cut i = true :=
    CompleteInteriorBranching.fullDirections_of_complete_nonleaf_total
      SkewTree.forwardAuxB T hcomplete hnonsingleton
      htotal cut hcut
      (CompleteInteriorBranching.nonleaf_of_height_lt
        SkewTree.forwardAuxB T hcomplete cut hcut hearly) i
  exact DirectionalSupport.descendant_of_uniqueBranch
    T cut i hbranch

/-- Every cut-child marker in the repaired literal R
has a uniquely assigned complete-support frontier. -/
theorem cut_child_unique_frontier
    {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (i : Fin b) :
    ∃! f : Node b,
      CutFrontier.Frontier T
        (fun u => ForwardAux u cut) f ∧
      IsPrefix (cut ++ [i]) f := by
  exact ForwardInclusiveFrontier.unique_frontier_complete_forward
    T hcomplete hnonsingleton cut (cut ++ [i])
    (cut_child_is_inclusive_boundary cut i)
    (cut_child_has_support_descendant
      T hcomplete hnonsingleton cut hcut hearly i)

end DualTree.ForwardMarkerFrontierCoverage
