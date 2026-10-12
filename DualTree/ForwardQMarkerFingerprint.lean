import DualTree.ForwardQObservableFingerprint
import DualTree.ForwardQMarkerSmoothPartition

/-!
# A literal signature-marker indexed smoothness fingerprint

The corrected Lemma 27 support geometry provides a proved bijection
from the actual signature-marker set R to the selected D2 coordinate
indices in the forward-sorted complete-support frontier.

For any subset B2 ⊆ R, put Gamma2 exactly at the D2 indices belonging
to B2 and Gamma1 at the complementary markers. This makes the
canonical observable fingerprint an explicit SOURCE-FACING record
indexed by the genuine signature markers, not an arbitrary guessed
coordinate partition.

We prove exact word-mask and point-observation identities at every
literal marker: B1=R\B2 keeps its full word but hides its marked
point; B2 preserves its point and outside-cone word and hides the
inside-cone symbols. Equality of the resulting marker fingerprint
is exactly Definition 21 smoothness for the induced partition.
The smooth-colouring factorization criterion holds for every
arbitrary colouring on the actual corrected starred W domain.

The substantial remaining proof is to construct a canonical ADDRESS
identification between Definition 24's abstract A=B1⊔B2 signature
and the literal R markers, and show that the paper's PARTICULAR
simple colouring factors through this record. This module does not
assert those unverified steps or any mixed-word span refinement.
-/

namespace DualTree.ForwardQMarkerFingerprint

open ForwardSourceQTree
open ForwardQMarkerSmoothPartition
open ForwardQObservableFingerprint

abbrev Marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQMarkerSmoothPartition.Marker c

/-- The canonical Q-observable record with Gamma2 selected by
literal corrected signature markers s ∈ B2 ⊆ R. -/
noncomputable def markerFingerprint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallback : α)
    (x : Input c) :
    ForwardQObservableFingerprint.Fingerprint c :=
  ForwardQObservableFingerprint.fingerprint c
    (gamma1OfMarkerB2 c B2) fallback x

/-- Full local word visibility at a literal B1 marker.
The marked point at this coordinate is NOT fixed. -/
theorem markerB1_mask_preserves_full_word
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallback : α)
    (x : Input c)
    (s : Marker c)
    (hs : s ∉ B2)
    (z : BoundedNode b (k - (m + 1))) :
    ForwardQObservableFingerprint.maskedLetter
      c (gamma1OfMarkerB2 c B2) fallback x
      (ForwardQMarkerCoverage.bulletForMarker c s).1 z =
    x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 z :=
  ForwardQObservableFingerprint.maskedLetter_gamma1
    c (gamma1OfMarkerB2 c B2) fallback x
    (ForwardQMarkerCoverage.bulletForMarker c s)
    ((gamma1_iff_not_B2 c B2 s).2 hs) z

/-- A literal B2 marker hides the input letter INSIDE the cone
of its unchanged local marked point. -/
theorem markerB2_mask_hides_inside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallback : α)
    (x : Input c)
    (s : Marker c)
    (hs : s ∈ B2)
    (z : BoundedNode b (k - (m + 1)))
    (hin : IsPrefix
      (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)).1
      z.1) :
    ForwardQObservableFingerprint.maskedLetter
      c (gamma1OfMarkerB2 c B2) fallback x
      (ForwardQMarkerCoverage.bulletForMarker c s).1 z = fallback :=
  ForwardQObservableFingerprint.maskedLetter_gamma2_inside
    c (gamma1OfMarkerB2 c B2) fallback x
    (ForwardQMarkerCoverage.bulletForMarker c s)
    ((gamma2_iff_B2 c B2 s).2 hs) z hin

/-- A literal B2 marker preserves the input letter OUTSIDE
its inclusive local marked cone. -/
theorem markerB2_mask_preserves_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallback : α)
    (x : Input c)
    (s : Marker c)
    (hs : s ∈ B2)
    (z : BoundedNode b (k - (m + 1)))
    (hout : ¬ IsPrefix
      (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)).1
      z.1) :
    ForwardQObservableFingerprint.maskedLetter
      c (gamma1OfMarkerB2 c B2) fallback x
      (ForwardQMarkerCoverage.bulletForMarker c s).1 z =
    x.words (ForwardQMarkerCoverage.bulletForMarker c s).1 z :=
  ForwardQObservableFingerprint.maskedLetter_gamma2_outside
    c (gamma1OfMarkerB2 c B2) fallback x
    (ForwardQMarkerCoverage.bulletForMarker c s)
    ((gamma2_iff_B2 c B2 s).2 hs) z hout

/-- A literal B1 marker's selected point is completely invisible
to the marker-derived observable fingerprint. -/
theorem markerB1_point_unobserved
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x : Input c)
    (s : Marker c)
    (hs : s ∉ B2) :
    ForwardQObservableFingerprint.observedPoint
      c (gamma1OfMarkerB2 c B2) x
      (ForwardQMarkerCoverage.bulletForMarker c s) = none := by
  have hg := (gamma1_iff_not_B2 c B2 s).2 hs
  simp [ForwardQObservableFingerprint.observedPoint, hg]

/-- A literal B2 marker records exactly its real local marked
point rather than merely its length or Q projected address. -/
theorem markerB2_point_recorded
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (x : Input c)
    (s : Marker c)
    (hs : s ∈ B2) :
    ForwardQObservableFingerprint.observedPoint
      c (gamma1OfMarkerB2 c B2) x
      (ForwardQMarkerCoverage.bulletForMarker c s) =
    some (x.bulletPoint (ForwardQMarkerCoverage.bulletForMarker c s)) := by
  have hg := (gamma2_iff_B2 c B2 s).2 hs
  simp [ForwardQObservableFingerprint.observedPoint, hg]

/-- Equality of the literal R/B2 marker fingerprint is EXACTLY
the smooth mixed-product equivalence for the corresponding
actual canonical selected D2 coordinate partition. -/
theorem markerFingerprint_eq_iff_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallback : α)
    (x y : Input c) :
    markerFingerprint c B2 fallback x =
      markerFingerprint c B2 fallback y ↔
      MixedProduct.SmoothRelated (gamma1OfMarkerB2 c B2) x y :=
  ForwardQObservableFingerprint.fingerprint_eq_iff_smooth
    c (gamma1OfMarkerB2 c B2) fallback x y

/-- A corrected-starred colouring is smooth for the specific
literal marker subset B2 precisely when it factors through
this real R-indexed observable record. The factor is total
on arbitrary fingerprints. -/
theorem markerSmoothStarred_iff_factors
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (B2 : Set (Marker c))
    (fallbackLetter : α)
    (fallbackColor : γ)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) :
    ForwardQStarredSmoothPartitions.SmoothStarredFor
        c (gamma1OfMarkerB2 c B2) color ↔
      ∃ f : ForwardQObservableFingerprint.Fingerprint c → γ,
        ∀ x : ForwardQActualStarredSpace.StarredInput c,
          color x = f (markerFingerprint c B2 fallbackLetter x.1) :=
  ForwardQObservableFingerprint.smoothStarred_iff_factors_through_fingerprint
    c (gamma1OfMarkerB2 c B2) fallbackLetter fallbackColor color

end DualTree.ForwardQMarkerFingerprint
