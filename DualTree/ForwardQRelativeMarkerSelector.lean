import DualTree.ForwardQLiteralMarkerLeafEquiv
import DualTree.ForwardQAmbientFibreLegalWord
import DualTree.ForwardQMeetClosed

/-!
# A canonical literal-R terminal observable on arbitrary starred outputs

The paper's Definition 24 uses an abstract canonical first-l-interior
boundary A. The globally forward-corrected Lemma 27 construction has
the literal signature boundary R and, by ForwardQLiteralMarkerLeafEquiv,
R is now known to index ALL terminal vertices of every actual Q output.

Fix the corrected source frame c and a literal marker r in R.
For an arbitrary starred output U, define its R-relative canonical
terminal as a terminal vertex above r if one exists, choosing
arbitrarily when there are multiple such vertices, and defaulting
to r itself if none exists.

For the SPECIFIC source-facing corrected Q output the choice is
proved unique: any leaf above r is exactly the projected leaf
P_(index r)(s_(index r)). This uses the first-exit boundary
antichain property of literal R together with the verified
classification of all Q terminal vertices.

Consequently the conditional Definition 24 colouring-transport
interface has a concrete marker map with no new input-specific
choices. This remains an R-RELATIVE notion of simplicity, not an
identification with the paper's canonical model boundary A.
-/

namespace DualTree.ForwardQRelativeMarkerSelector

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord

/-- At most one corrected Q terminal extends a given fixed
literal R first-exit boundary. Every terminal is a D2 projection
whose own recovered literal marker lies below it; the
antichain theorem forces that marker to equal r. -/
theorem Q_leaf_unique_above_literal_marker
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker c.source c.cut c.hout)
    (s : Node b)
    (hterminal :
      s ∈ (nodes c x).toList ∧
      s ∉ SkewTree.interior (nodes c x).toList)
    (hr : IsPrefix r.1 s) :
    s = (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c r)).1 := by
  let leaf : ForwardQLiteralMarkerLeafEquiv.QLeaf c x :=
    ⟨s, hterminal⟩
  obtain ⟨j, hproj⟩ :=
    ForwardQLiteralMarkerLeafEquiv.Q_leaf_has_bullet hb c x leaf
  have hmarked : IsPrefix (ForwardQMeetClosed.markerOfBullet c j).1 s := by
    rw [← hproj]
    exact ForwardQMeetClosed.recoveredMarker_prefix_projection c x j
  have hrBoundary :
      ForwardInclusiveFrontier.ForwardCutBoundary c.cut r.1 :=
    ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r.1 r.2
  have hjBoundary :
      ForwardInclusiveFrontier.ForwardCutBoundary c.cut
        (ForwardQMeetClosed.markerOfBullet c j).1 :=
    ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout
      (ForwardQMeetClosed.markerOfBullet c j).1
      (ForwardQMeetClosed.markerOfBullet c j).2
  have hmarker :
      r = ForwardQMeetClosed.markerOfBullet c j :=
    Subtype.ext
      (ForwardMarkerAntichain.eq_of_common_extension
        c.cut r.1 (ForwardQMeetClosed.markerOfBullet c j).1
        s hrBoundary hjBoundary hr hmarked)
  have hindex :
      ForwardQMarkerCoverage.bulletForMarker c r = j := by
    rw [hmarker]
    exact ForwardQMeetClosed.bulletForMarker_markerOfBullet c j
  rw [hindex]
  exact hproj.symm

/-- A shape-dependent, source-relative terminal marked by
the literal first-exit boundary r. On arbitrary starred
outputs no uniqueness is asserted; the fallback handles a
structure having no terminal above r. -/
noncomputable def canonicalTerminal
    {b n l k m : Nat} {α : Type*}
    (_c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (r : ForwardSortedMixedProduct.Marker
      _c.source _c.cut _c.hout) : Node b := by
  classical
  exact if h : ∃ t : Node b,
      t ∈ U.tree ∧
      t ∉ SkewTree.interior U.tree ∧
      IsPrefix r.1 t then
    Classical.choose h
  else r.1

/-- The abstract R-relative canonical terminal has the EXACT
projection prescribed by the actual forward-corrected Q,
for every enlarged starred input and every literal marker.
Thus the Q-specific canonical-marker transport premise of the
conditional smoothness lemma is discharged when A is R. -/
theorem canonicalTerminal_actual_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (r : ForwardSortedMixedProduct.Marker
      c.core.source c.core.cut c.core.hout) :
    canonicalTerminal c.core
      (fibreQStarredWord hb c fallback w) r =
      (markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux
          c.core fallback w.1)
        (ForwardQMarkerCoverage.bulletForMarker c.core r)).1 := by
  let erased : Input c.core :=
    ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1
  let q : Node b :=
    (markedProjection c.core erased
      (ForwardQMarkerCoverage.bulletForMarker c.core r)).1
  have hmem :
      q ∈ (fibreQStarredWord hb c fallback w).tree := by
    rw [fibreQStarredWord_tree]
    exact Finset.mem_toList.mpr
      (markedProjection_mem c.core erased
        (ForwardQMarkerCoverage.bulletForMarker c.core r))
  have hterminal :
      q ∉ SkewTree.interior (fibreQStarredWord hb c fallback w).tree := by
    rw [fibreQStarredWord_tree]
    exact ForwardQSourceTerminals.markedProjection_terminal
      c.core erased
      (ForwardQMarkerCoverage.bulletForMarker c.core r)
  have hprefix : IsPrefix r.1 q :=
    ForwardQMarkerCoverage.marker_prefix_projected_point
      c.core erased r
  have hex :
      ∃ t : Node b,
        t ∈ (fibreQStarredWord hb c fallback w).tree ∧
        t ∉ SkewTree.interior (fibreQStarredWord hb c fallback w).tree ∧
        IsPrefix r.1 t :=
    ⟨q, hmem, hterminal, hprefix⟩
  unfold canonicalTerminal
  rw [dif_pos hex]
  have hchosen := Classical.choose_spec hex
  have hchosenLeaf :
      Classical.choose hex ∈ (nodes c.core erased).toList ∧
      Classical.choose hex ∉ SkewTree.interior (nodes c.core erased).toList := by
    simpa only [fibreQStarredWord_tree] using
      And.intro hchosen.1 hchosen.2.1
  exact Q_leaf_unique_above_literal_marker
    hb c.core erased r (Classical.choose hex)
    hchosenLeaf hchosen.2.2

end DualTree.ForwardQRelativeMarkerSelector
