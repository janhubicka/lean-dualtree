import DualTree.CompleteInteriorBranching

/-!
# Marker antichain for the inclusive support cut in Lemma 27

Two distinct first-exit points from an initial segment cannot lie
on one ambient branch. This proves the *at most one* half of the
marker-to-frontier correspondence without using complete skewness.
-/

namespace DualTree.MarkerAntichain

/-- Inclusive-cut boundary points form an antichain under prefix. -/
theorem eq_of_prefix_boundaries {b : Nat}
    (cut s t : Node b)
    (hs : InclusiveFrontier.PaperCutBoundary cut s)
    (ht : InclusiveFrontier.PaperCutBoundary cut t)
    (hst : IsPrefix s t) :
    s = t := by
  by_contra hne
  exact hs.1 (ht.2 s ⟨hst, hne⟩)

/-- No ambient cone can contain two distinct candidate signature markers. -/
theorem unique_candidate_marker_in_cone
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s t f : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout)
    (ht : t ∈ SignatureMarker.coneMarkers O cut hout)
    (hsf : IsPrefix s f)
    (htf : IsPrefix t f) :
    s = t := by
  have hbs := InclusiveSignatureMarkers.coneMarker_paperCutBoundary
    O cut hout hs
  have hbt := InclusiveSignatureMarkers.coneMarker_paperCutBoundary
    O cut hout ht
  rcases le_total s.length t.length with hle | hle
  · exact eq_of_prefix_boundaries cut s t hbs hbt
      (CutFrontier.prefix_of_prefix_length_le hsf htf hle)
  · exact (eq_of_prefix_boundaries cut t s hbt hbs
      (CutFrontier.prefix_of_prefix_length_le htf hsf hle)).symm

end DualTree.MarkerAntichain
