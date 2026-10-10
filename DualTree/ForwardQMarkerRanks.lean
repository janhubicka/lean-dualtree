import DualTree.ForwardQIntrinsicRanks
import DualTree.ForwardQMarkerCoverage

/-!
# Intrinsic Q rank of each sorted literal marker projection

The current source-facing forward Q support has the exact old interior
as fixed base and one projected terminal node per selected D₂ marker.

For a genuine literal marker r∈R, its first-exit boundary property
implies a useful *prefix-mask invariance*: every old interior node
s lies at/before the inclusive forward cut, while r lies outside.
If both s and r prefix the new projected point P(r), then s
must already be a strict prefix of r. Conversely, every strict
old-interior prefix of r prefixes P(r).

Consequently the Q-intrinsic rank of P(r) is exactly the number
of original interior vertices properly preceding the literal marker r.
It is not the complete-T intrinsic rank of P(r) and is independent
of its safe local D₂ tail.

This is the main rank input for the forward repaired skew clauses
(ii) and (iii), still to be combined with the cross-rank ambient
length comparisons of old and projected nodes.
-/

namespace DualTree.ForwardQMarkerRanks

open ForwardSourceQTree

/-- Original interior nodes have exactly the same prefix relation
to a literal marker and to that marker's genuine projected Q point. -/
theorem oldBase_strictPrefix_projection_iff_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (s : Node b)
    (hs : s ∈ oldBase c) :
    IsStrictPrefix s
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c r)).1 ↔
      IsStrictPrefix s r.1 := by
  let p := (markedProjection c x
    (ForwardQMarkerCoverage.bulletForMarker c r)).1
  have hrp : IsPrefix r.1 p :=
    ForwardQMarkerCoverage.marker_prefix_projected_point c x r
  have hsEarly : ForwardAux s c.cut :=
    ForwardQFixedBase.oldBase_before_cut c s hs
  have hrOutside : ¬ ForwardAux r.1 c.cut :=
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r.1 r.2).1
  constructor
  · intro hsp
    by_cases hlen : s.length < r.1.length
    · have hsr : IsPrefix s r.1 :=
        CutFrontier.prefix_of_prefix_length_le
          hsp.1 hrp (Nat.le_of_lt hlen)
      exact ⟨hsr, by
        intro heq
        have heqlen := congrArg List.length heq
        omega⟩
    · have hle : r.1.length ≤ s.length := by omega
      have hrs : IsPrefix r.1 s :=
        CutFrontier.prefix_of_prefix_length_le hrp hsp.1 hle
      have hrEarly : ForwardAux r.1 c.cut :=
        ForwardInclusiveFrontier.forwardAux_of_prefix hrs hsEarly
      exact False.elim (hrOutside hrEarly)
  · intro hsr
    exact Lemma27QInterior.strictPrefix_trans_prefix hsr hrp

/-- A projected D₂ literal marker has Q intrinsic rank equal
to the number of old source interior nodes that strictly
precede the *literal marker*, not the projected ambient point. -/
theorem markedProjection_height_eq_marker_prefix_card
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout) :
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c r)).1 =
      ((SkewTree.interior c.source.tree).toFinset.filter
        (fun s => SkewTree.strictPrefixB s r.1 = true)).card := by
  classical
  let p := (markedProjection c x
    (ForwardQMarkerCoverage.bulletForMarker c r)).1
  have hp : p ∈ nodes c x :=
    markedProjection_mem c x
      (ForwardQMarkerCoverage.bulletForMarker c r)
  rw [ForwardQIntrinsicRanks.Q_height_eq_original_interior_prefix_card
    c x p hp]
  have hset :
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun s => SkewTree.strictPrefixB s p = true) =
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun s => SkewTree.strictPrefixB s r.1 = true) := by
    ext s
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hs, hsp⟩
      have hsBase : s ∈ oldBase c :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).2 hs
      have hh := (oldBase_strictPrefix_projection_iff_marker
        c x r s hsBase).1
        ((SkewBranchGeometry.strictPrefixB_iff s p).1 hsp)
      exact ⟨hs, (SkewBranchGeometry.strictPrefixB_iff s r.1).2 hh⟩
    · rintro ⟨hs, hsr⟩
      have hsBase : s ∈ oldBase c :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).2 hs
      have hh := (oldBase_strictPrefix_projection_iff_marker
        c x r s hsBase).2
        ((SkewBranchGeometry.strictPrefixB_iff s r.1).1 hsr)
      exact ⟨hs, (SkewBranchGeometry.strictPrefixB_iff s p).2 hh⟩
  exact congrArg Finset.card hset

/-- Two literal markers with the same set of old-interior
prefixes yield Q-projected leaves at the same intrinsic
height, regardless of their distinct local D₂ depths. -/
theorem equal_Q_height_of_equal_marker_masks
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r t : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (hmasks : ∀ s, s ∈ SkewTree.interior c.source.tree →
      (IsStrictPrefix s r.1 ↔ IsStrictPrefix s t.1)) :
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c r)).1 =
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c t)).1 := by
  rw [markedProjection_height_eq_marker_prefix_card c x r,
    markedProjection_height_eq_marker_prefix_card c x t]
  apply congrArg Finset.card
  ext s
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hs, hsr⟩
    exact ⟨hs, (SkewBranchGeometry.strictPrefixB_iff s t.1).2
      ((hmasks s hs).1
        ((SkewBranchGeometry.strictPrefixB_iff s r.1).1 hsr))⟩
  · rintro ⟨hs, hst⟩
    exact ⟨hs, (SkewBranchGeometry.strictPrefixB_iff s r.1).2
      ((hmasks s hs).2
        ((SkewBranchGeometry.strictPrefixB_iff s t.1).1 hst))⟩

end DualTree.ForwardQMarkerRanks
