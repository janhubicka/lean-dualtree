import DualTree.ForwardQRooted
import DualTree.InteriorMarkerMeet
import DualTree.ForwardMarkerAntichain

/-!
# Ambient meets of the forward-corrected literal signature skeleton

The original Lemma 27 proof uses the ambient meet of two distinct
vertices in the literal signature skeleton.  A prefix-poset
isomorphism does *not* automatically preserve actual ambient meets;
we therefore verify the source geometry before transferring it to Q.

Let S be a semi-complete skew source for the globally corrected
forward auxiliary order and let R be its actual corrected signature
marker set. We prove:
* S is ambient meet-closed, using the generic semi-complete tree
  theorem and totality of the forward auxiliary order;
* every literal r∈R has a source S-descendant (not just a descendant
  in the enclosing complete support T);
* markers R form an ambient prefix antichain and no marker
  prefixes an original interior node;
* the meet of any distinct nodes in Int(S)∪R is in Int(S).

Thus the full *source-side* literal skeleton is ambient meet-closed.
The Q-side meet-transport step will be checked separately, without
silently treating a prefix isomorphism as an ambient meet isomorphism.
-/

namespace DualTree.ForwardQLiteralSkeletonMeets

open ForwardSourceQTree

/-- The repaired forward semi-complete source is ambient meet-closed,
without importing the source-specific reverse-order variant. -/
theorem source_meetClosed
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    MeetGeometry.MeetClosed c.source.tree := by
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hroot : SkewTree.rootedB c.source.tree = true :=
    CompleteSkewMeet.rootedB_of_skew_nonSingleton
      SkewTree.forwardAuxB c.source.tree hparts.1
      (ForwardQRooted.source_nonsingleton c)
  have htotal :
      ∀ s t : Node b, s ≠ t →
        SkewTree.forwardAuxB s t = true ∨
        SkewTree.forwardAuxB t s = true := by
    intro s t _
    rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  have hunique :
      MeetClosedFromBranching.AtMostOneDirection c.source.tree :=
    SemiCompleteSkewMeet.atMostOneDirection_of_semiComplete_total
      SkewTree.forwardAuxB c.source.tree c.source.semi_complete
      (ForwardQRooted.source_nonsingleton c) htotal
  exact MeetClosedFromBranching.meetClosed_of_rooted_uniqueDirections
    c.source.tree hroot hunique

/-- Every ambient direction at the last original interior cut
has an immediate source successor: semi-completeness, not the
stronger k-complete enclosing support, supplies this fact. -/
theorem cut_full_directions
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Fin b) :
    SkewTree.uniqueBranchB c.source.tree c.cut i = true := by
  have hcutMem : c.cut ∈ c.source.tree :=
    (List.mem_filter.mp c.hcut).1
  have hnonleaf :
      (SkewTree.immediateSuccs c.source.tree c.cut).length ≠ 0 := by
    have htest := (List.mem_filter.mp c.hcut).2
    cases hlist : SkewTree.immediateSuccs c.source.tree c.cut with
    | nil => simp [hlist] at htest
    | cons u us => simp [hlist]
  have htotal :
      ∀ s t : Node b, s ≠ t →
        SkewTree.forwardAuxB s t = true ∨
        SkewTree.forwardAuxB t s = true := by
    intro s t _
    rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  exact SemiCompleteSkewMeet.fullDirections_of_semiComplete_nonleaf_total
    SkewTree.forwardAuxB c.source.tree c.source.semi_complete
    (ForwardQRooted.source_nonsingleton c) htotal
    c.cut hcutMem hnonleaf i

/-- Both kinds of actual forward signature marker have a descendant
in the original semi-complete source, not merely in the ambient T. -/
theorem literalMarker_has_source_descendant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b)
    (hr : r ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout) :
    ∃ t, t ∈ c.source.tree ∧ IsPrefix r t := by
  classical
  have hr' :
      r ∈ (ForwardStarredSignature.signatureTerminalMarkers
        c.source c.cut c.hout ++
        (SkewTree.allFin b).map
          (fun i => c.cut ++ [i])).dedup := by
    simpa [ForwardStarredSignature.literalR] using hr
  simp only [List.mem_dedup, List.mem_append] at hr'
  rcases hr' with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        c.source c.cut c.hcut c.hmax c.hout r hterminal
    refine ⟨t.1,
      (StarredSignature.exceptionalLeaves_spec
        c.source c.cut t.1 t.2).1, ?_⟩
    rw [← ht]
    exact (ForwardSignatureBoundary.firstBoundary_spec
      c.cut t.1 (c.hout t.1 t.2)).1
  · obtain ⟨i, _hi, hchildEq⟩ := List.mem_map.mp hchild
    rw [← hchildEq]
    exact DirectionalSupport.descendant_of_uniqueBranch
      c.source.tree c.cut i (cut_full_directions c i)

/-- The literal forward signature markers form an ambient prefix
antichain by their common inclusive first-exit boundary property. -/
theorem literalR_antichain
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r s : Node b)
    (hr : r ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout)
    (hs : s ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout)
    (hrs : IsPrefix r s) :
    r = s := by
  exact ForwardMarkerAntichain.eq_of_prefix_boundaries
    c.cut r s
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r hr)
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout s hs)
    hrs

/-- A literal first-exit marker cannot be a prefix of an original
interior vertex, since every original interior is at/before cut. -/
theorem literalR_not_prefix_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b)
    (hr : r ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout)
    (u : Node b)
    (hu : u ∈ SkewTree.interior c.source.tree) :
    ¬ IsPrefix r u := by
  intro hru
  have hrOutside : ¬ ForwardAux r c.cut :=
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r hr).1
  have huBefore : ForwardAux u c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax u hu
  exact hrOutside
    (ForwardInclusiveFrontier.forwardAux_of_prefix hru huBefore)

/-- The ambient meet of any two *distinct* nodes of the literal
source skeleton Int(S)∪R belongs to the original interior Int(S). -/
theorem distinct_skeleton_meet_in_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : Node b)
    (hu : u ∈ SkewTree.interior c.source.tree ∨
      u ∈ ForwardStarredSignature.literalR c.source c.cut c.hout)
    (hv : v ∈ SkewTree.interior c.source.tree ∨
      v ∈ ForwardStarredSignature.literalR c.source c.cut c.hout)
    (hne : u ≠ v) :
    MeetGeometry.commonPrefix u v ∈
      SkewTree.interior c.source.tree := by
  exact InteriorMarkerMeet.meet_distinct_interior_union_markers
    c.source.tree
    (ForwardStarredSignature.literalR c.source c.cut c.hout)
    (source_meetClosed c)
    (literalMarker_has_source_descendant c)
    (literalR_antichain c)
    (literalR_not_prefix_interior c)
    hu hv hne

/-- The literal source-side signature skeleton Int(S)∪R is
closed under ambient longest-common-prefix meets. -/
theorem sourceSkeleton_meetClosed
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    MeetGeometry.MeetClosed
      (SkewTree.interior c.source.tree ++
        ForwardStarredSignature.literalR c.source c.cut c.hout) := by
  exact InteriorMarkerMeet.meetClosed_interior_union_markers
    c.source.tree
    (ForwardStarredSignature.literalR c.source c.cut c.hout)
    (source_meetClosed c)
    (literalMarker_has_source_descendant c)
    (literalR_antichain c)
    (literalR_not_prefix_interior c)

end DualTree.ForwardQLiteralSkeletonMeets
