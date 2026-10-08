import DualTree.MeetGeometry
import DualTree.StarredSignature
import DualTree.SignatureBoundary

/-!
# Support descendants of signature boundary markers

The paper's R in Lemma 27 combines:
(1) boundary nodes coming from exceptional leaves of S (as in Definition 26),
(2) the b ambient immediate successors of the distinguished support node t0.

Here is the finite existence argument. The first kind has a support descendant
because the original starred tree S lies inside the ambient support T. The
second kind has a descendant because T branches in every direction at t0.

The latter branching assertion is retained as an explicit hypothesis until
the complete-skew support API supplies it. This module verifies existence,
not uniqueness of the frontier or equality with the literal set R: the
latter also requires proving distinctness of the selected boundary markers.
-/

namespace DualTree.SignatureMarker

/-- The exceptional-leaf boundary markers from the signature skeleton. -/
noncomputable def boundaryMarkers
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) := by
  classical
  exact (StarredSignature.exceptionalLeaves O cut).attach.map
    (fun t => SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2))

/-- Each exceptional boundary is a prefix of a leaf of S. -/
theorem boundaryMarker_has_leaf
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ boundaryMarkers O cut hout) :
    ∃ t, t ∈ O.tree ∧ IsPrefix s t := by
  classical
  unfold boundaryMarkers at hs
  rcases List.mem_map.mp hs with ⟨t, ht, heq⟩
  have hleaf : t.1 ∈ O.tree :=
    (StarredSignature.exceptionalLeaves_spec O cut t.1 t.2).1
  have hp : IsPrefix
      (SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2)) t.1 :=
    (SignatureBoundary.firstBoundary_spec cut t.1 (hout t.1 t.2)).1
  refine ⟨t.1, hleaf, ?_⟩
  rw [← heq]
  exact hp

/-- All boundary markers have support descendants when S ⊆ T. -/
theorem boundaryMarker_has_support_descendant
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    {s : Node b}
    (hs : s ∈ boundaryMarkers O cut hout) :
    ∃ t, t ∈ T ∧ IsPrefix s t := by
  rcases boundaryMarker_has_leaf O cut hout hs with ⟨t, ht, hst⟩
  exact ⟨t, hST t ht, hst⟩

/-- All potentially relevant frontier-cone markers. -/
noncomputable def coneMarkers
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) :=
  boundaryMarkers O cut hout ++
    (SkewTree.allFin b).map (fun i => cut ++ [i])

/--
Every cone marker has a support descendant, provided the star tree is
inside T and T has a descendant in each branch direction at the cut.
-/
theorem coneMarker_has_support_descendant
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hbranches : ∀ i : Fin b,
      ∃ t, t ∈ T ∧ IsPrefix (cut ++ [i]) t)
    {s : Node b}
    (hs : s ∈ coneMarkers O cut hout) :
    ∃ t, t ∈ T ∧ IsPrefix s t := by
  unfold coneMarkers at hs
  rcases List.mem_append.mp hs with hboundary | hchild
  · exact boundaryMarker_has_support_descendant
      O cut hout T hST hboundary
  · rcases List.mem_map.mp hchild with ⟨i, _hi, heq⟩
    rcases hbranches i with ⟨t, ht, hp⟩
    refine ⟨t, ht, ?_⟩
    rw [← heq]
    exact hp

end DualTree.SignatureMarker
