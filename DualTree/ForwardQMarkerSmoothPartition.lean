import DualTree.ForwardQStarredSmoothPartitions
import DualTree.ForwardQMeetClosed

/-!
# Transport a marker partition onto actual sorted D₂ coordinates

The genuine forward-corrected Lemma 27 frame has a literal set R of
signature boundary/cut-child markers. Previous results establish a
bijection from R to the actual selected D₂ indices of the sorted
complete-support frontier. A split R = B1 ⊔ B2 can therefore induce
the Gamma₁/Gamma₂ split required by Definition 21.

This file defines that transport and establishes the precise two
types of consequences of mixed-product smoothness:

* B1 markers correspond to Gamma₁; their FULL local coordinate
  words agree while their marked points may move.
* B2 markers correspond to Gamma₂; their local marked points and
  outside-cone word values agree. Their actual projected Q nodes
  agree as well, because projected nodes are computed from points.

This is a structural bridge on the literal R marker type. It does
not yet prove that Definition 24's CANONICAL A/B1/B2 markers match
the signature R markers, or that the particular printed Q word
transports their simple-colouring hypotheses. The associated
forward-sorted coordinate correction is explicit.
-/

namespace DualTree.ForwardQMarkerSmoothPartition

open ForwardSourceQTree

abbrev Marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardSortedMixedProduct.Marker c.source c.cut c.hout

/-- Every genuine literal R marker is recovered after taking
its corresponding real selected D₂ coordinate. -/
theorem markerOfBullet_bulletForMarker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Marker c) :
    ForwardQMeetClosed.markerOfBullet c
      (ForwardQMarkerCoverage.bulletForMarker c s) = s := by
  have hinj :=
    (ForwardSortedMixedProduct.bulletIndex_bijective
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly).1
  apply hinj
  exact ForwardQMeetClosed.bulletForMarker_markerOfBullet c
    (ForwardQMarkerCoverage.bulletForMarker c s)

/-- Encode B₂ as Gamma₂ (false), and its complement B₁
as Gamma₁ (true), through the genuine marker-bullet bijection. -/
noncomputable def gamma1OfMarkerB2
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c)) :
    MixedProduct.BulletIndex (kind c) → Bool := by
  classical
  exact fun i => decide (ForwardQMeetClosed.markerOfBullet c i ∉ B2)

/-- A particular literal marker receives its intended
Gamma₁/Gamma₂ membership, with no possible permutation
or duplicate coordinate in the sorted D₂ family. -/
theorem gamma1_at_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (s : Marker c) :
    gamma1OfMarkerB2 c B2
      (ForwardQMarkerCoverage.bulletForMarker c s) =
        decide (s ∉ B2) := by
  classical
  simp [gamma1OfMarkerB2, markerOfBullet_bulletForMarker]

/-- Gamma₁ is precisely the complement of the selected
B₂ marker set in the actual (sorted) D₂ coordinate domain. -/
theorem gamma1_iff_not_B2
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (s : Marker c) :
    gamma1OfMarkerB2 c B2
      (ForwardQMarkerCoverage.bulletForMarker c s) = true ↔
      s ∉ B2 := by
  classical
  rw [gamma1_at_marker]
  simp

/-- Gamma₂ membership is exact literal B₂ marker membership. -/
theorem gamma2_iff_B2
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (s : Marker c) :
    gamma1OfMarkerB2 c B2
      (ForwardQMarkerCoverage.bulletForMarker c s) = false ↔
      s ∈ B2 := by
  classical
  rw [gamma1_at_marker]
  simp

/-- A smooth comparison for this marker split fixes the entire
local word at every B₁-marked selected coordinate. -/
theorem gamma1_marker_words_equal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (gamma1OfMarkerB2 c B2) x y)
    (s : Marker c) (hs : s ∉ B2) :
    x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 =
      y.words (ForwardQMarkerCoverage.bulletForMarker c s).1 := by
  have hgamma :
      gamma1OfMarkerB2 c B2
        (ForwardQMarkerCoverage.bulletForMarker c s) = true :=
    (gamma1_iff_not_B2 c B2 s).2 hs
  simpa [hgamma] using
    hxy.2.2 (ForwardQMarkerCoverage.bulletForMarker c s)

/-- The same smooth comparison fixes the local D₂ marked point
on every B₂-marked coordinate, but NOT its inside-cone letters. -/
theorem gamma2_marker_points_equal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (gamma1OfMarkerB2 c B2) x y)
    (s : Marker c) (hs : s ∈ B2) :
    x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) =
      y.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) := by
  have hgamma :
      gamma1OfMarkerB2 c B2
        (ForwardQMarkerCoverage.bulletForMarker c s) = false :=
    (gamma2_iff_B2 c B2 s).2 hs
  have hpair :
      x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) =
        y.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) ∧
      ∀ t : BoundedNode b (k - (m + 1)),
        ¬ IsPrefix
          (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)).1 t.1 →
          x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t =
          y.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t := by
    simpa [hgamma] using
      hxy.2.2 (ForwardQMarkerCoverage.bulletForMarker c s)
  exact hpair.1

/-- At a B₂ marker the words agree everywhere OUTSIDE
the cone of its unchanged marked point. -/
theorem gamma2_marker_words_outside_equal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (gamma1OfMarkerB2 c B2) x y)
    (s : Marker c) (hs : s ∈ B2)
    (t : BoundedNode b (k - (m + 1)))
    (ht : ¬ IsPrefix
      (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)).1 t.1) :
    x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t =
      y.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t := by
  have hgamma :
      gamma1OfMarkerB2 c B2
        (ForwardQMarkerCoverage.bulletForMarker c s) = false :=
    (gamma2_iff_B2 c B2 s).2 hs
  have hpair :
      x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) =
        y.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s) ∧
      ∀ t : BoundedNode b (k - (m + 1)),
        ¬ IsPrefix
          (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)).1 t.1 →
          x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t =
          y.words (ForwardQMarkerCoverage.bulletForMarker c s).1 t := by
    simpa [hgamma] using
      hxy.2.2 (ForwardQMarkerCoverage.bulletForMarker c s)
  exact hpair.2 t ht

/-- The fixed B₂ local point projects to the identical actual
Q marked node at its genuine forward-sorted frontier coordinate.
This is the geometric half of condition (ii) of simplicity,
conditional on identifying the canonical A-marker in Definition 24. -/
theorem gamma2_Q_projected_marker_equal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (gamma1OfMarkerB2 c B2) x y)
    (s : Marker c) (hs : s ∈ B2) :
    markedProjection c x (ForwardQMarkerCoverage.bulletForMarker c s) =
      markedProjection c y (ForwardQMarkerCoverage.bulletForMarker c s) := by
  have hp := gamma2_marker_points_equal c B2 x y hxy s hs
  simp only [markedProjection, hp]

end DualTree.ForwardQMarkerSmoothPartition
