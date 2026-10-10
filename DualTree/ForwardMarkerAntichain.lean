import DualTree.ForwardInclusiveFrontier

/-!
# Antichains and collision-free coordinates at the forward inclusive cut

The corrected signature's literal marker set R must inject into the
minimal support frontiers. Mere existence and uniqueness of a frontier
for each marker do not prove this: different markers might be sent
to the same frontier.

The key geometric fact is simpler. Every *boundary* of the inclusive
forward auxiliary cut has all proper ambient prefixes in the cut.
Two such boundaries cannot be comparable in the prefix order.
Consequently two boundaries lying below the same frontier coincide.

This file proves the abstract boundary antichain and the resulting
injectivity principle. A source-facing follow-up must prove that every
point of the corrected literal R is such a boundary, then attach the
actual unique-frontier choice of Lemma 27.
-/

namespace DualTree.ForwardMarkerAntichain

/-- Comparable first-exit boundaries of the inclusive forward cut
are the same ambient word. -/
theorem eq_of_prefix_boundaries {b : Nat}
    (cut s t : Node b)
    (hs : ForwardInclusiveFrontier.ForwardCutBoundary cut s)
    (ht : ForwardInclusiveFrontier.ForwardCutBoundary cut t)
    (hst : IsPrefix s t) :
    s = t := by
  by_contra hne
  exact hs.1 (ht.2 s ⟨hst, hne⟩)

/-- Different inclusive forward-cut boundaries cannot both lie
below one common ambient node. -/
theorem eq_of_common_extension {b : Nat}
    (cut s t f : Node b)
    (hs : ForwardInclusiveFrontier.ForwardCutBoundary cut s)
    (ht : ForwardInclusiveFrontier.ForwardCutBoundary cut t)
    (hsf : IsPrefix s f) (htf : IsPrefix t f) :
    s = t := by
  rcases le_total s.length t.length with hle | hle
  · exact eq_of_prefix_boundaries cut s t hs ht
      (CutFrontier.prefix_of_prefix_length_le hsf htf hle)
  · exact (eq_of_prefix_boundaries cut t s ht hs
      (CutFrontier.prefix_of_prefix_length_le htf hsf hle)).symm

/-- Any assignment of a forward-cut frontier extending each
marked boundary is injective, as soon as the marker labels
are injective. No auxiliary-order comparison between frontier
nodes is needed. -/
theorem assignment_injective
    {b : Nat} {M : Type*}
    (cut : Node b)
    (marker : M → Node b)
    (hmarker : Function.Injective marker)
    (hboundary :
      ∀ x : M,
        ForwardInclusiveFrontier.ForwardCutBoundary cut (marker x))
    (frontier : M → Node b)
    (hprefix : ∀ x : M, IsPrefix (marker x) (frontier x)) :
    Function.Injective frontier := by
  intro x y hxy
  apply hmarker
  apply eq_of_common_extension cut (marker x) (marker y) (frontier x)
    (hboundary x) (hboundary y)
    (hprefix x)
  simpa [hxy] using hprefix y

/-- For the literal marker list, unique first-exit boundaries plus
an extending frontier choice give injective marker coordinates. -/
theorem boundary_list_frontier_injective
    {b : Nat} (R : List (Node b)) (cut : Node b)
    (hboundary : ∀ s, s ∈ R →
      ForwardInclusiveFrontier.ForwardCutBoundary cut s)
    (frontier : {s : Node b // s ∈ R} → Node b)
    (hprefix : ∀ s, IsPrefix s.1 (frontier s)) :
    Function.Injective frontier := by
  exact assignment_injective cut Subtype.val
    (fun x y h => Subtype.ext h)
    (fun s => hboundary s.1 s.2)
    frontier hprefix

end DualTree.ForwardMarkerAntichain
