import DualTree.ForwardSourceQTree
import DualTree.ForwardLiteralFrontierCoordinates
import DualTree.ForwardSortedMixedProduct

/-!
# Every literal signature marker has an actual descendant in corrected Q

The corrected Lemma 27 marker type R consists of genuine first-exit
boundaries of the forward auxiliary cut. Every marker r has a unique
support frontier f extending it, and the sorted frontier coordinate
map assigns r a unique D₂/bullet coordinate i.

The actual source-facing corrected Q tree is built from projected
bullet points P_i(s_i). The forward canonical cone theorem proves
f is a prefix of P_i(s_i). Therefore each literal r has an actual
Q-support descendant.

This supplies the bridge from the corrected signature's immediate
successors to the reconstructed Q tree. The converse inclusion of
interiors will be handled separately using exact signature interior
persistence. The height/order axioms and the word part remain open.
-/

namespace DualTree.ForwardQMarkerCoverage

open ForwardSourceQTree

/-- The actual bullet index selected for a literal corrected
signature marker by the sorted frontier coordinate injection. -/
noncomputable def bulletForMarker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : ForwardSortedMixedProduct.Marker c.source c.cut c.hout) :
    MixedProduct.BulletIndex (kind c) :=
  MixedProduct.bulletIndex
    (ForwardSortedMixedProduct.index
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly) s

/-- The frontier root of the selected bullet coordinate is
exactly the unique minimal support frontier of its literal R
marker, not merely some member of the same cone. -/
theorem bullet_frontier_eq_marker_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : ForwardSortedMixedProduct.Marker c.source c.cut c.hout) :
    (ForwardOrderedProjections.frontierAt
      c.T c.cut (bulletForMarker c s).1).1 =
    ForwardLiteralFrontierCoordinates.frontierFor
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly s := by
  change (ForwardSortedFrontiers.frontiers c.T c.cut).get
    (ForwardSortedFrontiers.coordinate
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly s) =
    ForwardLiteralFrontierCoordinates.frontierFor
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly s
  exact ForwardSortedFrontiers.coordinate_frontier
    c.source c.cut c.hcut c.hmax c.hout
    c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly s

/-- Every literal R marker is an ambient prefix of the
projected node at its exact sorted D₂ coordinate. -/
theorem marker_prefix_projected_point
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : ForwardSortedMixedProduct.Marker c.source c.cut c.hout) :
    IsPrefix s.1 (markedProjection c x (bulletForMarker c s)).1 := by
  have hsFront :=
    (ForwardLiteralFrontierCoordinates.frontierFor_spec
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly s).2
  have hproj := markedProjection_cone c x (bulletForMarker c s)
  rw [bullet_frontier_eq_marker_frontier c s] at hproj
  exact isPrefix_trans hsFront hproj

/-- Every literal corrected marker has a concrete descendant
among the actual nodes of the repaired source-facing Q tree. -/
theorem literalMarker_has_Q_descendant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ ForwardLiteralFrontierCoordinates.R
      c.source c.cut c.hout) :
    ∃ t : Node b, t ∈ nodes c x ∧ IsPrefix s t := by
  let marker : ForwardSortedMixedProduct.Marker
    c.source c.cut c.hout := ⟨s, hs⟩
  let i := bulletForMarker c marker
  exact ⟨(markedProjection c x i).1,
    markedProjection_mem c x i,
    marker_prefix_projected_point c x marker⟩

/-- If a source node lies strictly below a literal corrected
marker, it retains a strict Q descendant as well. -/
theorem strict_Q_descendant_of_literal_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s r : Node b)
    (hsr : IsStrictPrefix s r)
    (hr : r ∈ ForwardLiteralFrontierCoordinates.R
      c.source c.cut c.hout) :
    ∃ t, t ∈ nodes c x ∧ IsStrictPrefix s t := by
  obtain ⟨t, ht, hrt⟩ :=
    literalMarker_has_Q_descendant c x r hr
  refine ⟨t, ht, isPrefix_trans hsr.1 hrt, ?_⟩
  intro hst
  have hlen1 :=
    MeetClosedFromBranching.length_lt_of_strictPrefix hsr
  have hlen2 := prefix_length_le hrt
  rw [← hst] at hlen2
  omega

/-- If b is positive, the cut has an explicit strict
descendant in the actual Q support: use any one of its
literal child markers in R. -/
theorem cut_has_strict_Q_descendant
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    ∃ t, t ∈ nodes c x ∧ IsStrictPrefix c.cut t := by
  let i : Fin b := ⟨0, hb⟩
  have hr : c.cut ++ [i] ∈
      ForwardLiteralFrontierCoordinates.R c.source c.cut c.hout :=
    ForwardStarredSignature.cut_child_mem_literalR
      c.source c.cut c.hout i
  have hstrict : IsStrictPrefix c.cut (c.cut ++ [i]) := by
    refine ⟨⟨[i], rfl⟩, ?_⟩
    intro h
    have hh := congrArg List.length h
    simp at hh
  exact strict_Q_descendant_of_literal_marker
    c x c.cut (c.cut ++ [i]) hstrict hr

end DualTree.ForwardQMarkerCoverage
