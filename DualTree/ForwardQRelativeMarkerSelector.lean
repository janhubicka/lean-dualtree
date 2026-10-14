import DualTree.ForwardQLiteralMarkerLeafEquiv
import DualTree.ForwardQAmbientFibreLegalWord
import DualTree.ForwardQMeetClosed
import DualTree.ForwardQMarkerSmoothPartition
import DualTree.ForwardQMarkerTransportInterface

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
  change (markedProjection c x j).1 = s at hproj
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


/-- Specialize the general canonical-marker simplicity interface to
the ACTUAL literal corrected source boundary R. The R-to-D2
indexing equivalence and canonical terminal identity have now
both been constructed, rather than postulated.

This is an R-RELATIVE simplicity result. It does not assert that
the paper's separate model boundary A has yet been identified
with R or that arbitrary Definition 24-simple colourings satisfy
this particular R-indexed simplicity predicate. -/
theorem relativeR_simple_pullback_smooth
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (B2 : Set (ForwardQMarkerSmoothPartition.Marker c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (canonicalTerminal c.core)
        (fun r => r ∈ B2) color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2)
      x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  have hpartition :
      ∀ r : ForwardQMarkerSmoothPartition.Marker c.core,
        r ∈ B2 ↔
          ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
            c.core B2
            ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
              c.core) r) = false := by
    intro r
    change r ∈ B2 ↔
      ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2
        (ForwardQMarkerCoverage.bulletForMarker c.core r) = false
    exact
      (ForwardQMarkerSmoothPartition.gamma2_iff_B2 c.core B2 r).symm
  have hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback)
        (r : ForwardQMarkerSmoothPartition.Marker c.core),
        canonicalTerminal c.core
          (fibreQStarredWord hb c fallback w) r =
        (markedProjection c.core
          (ForwardQEnlargedConstantWords.eraseAux
            c.core fallback w.1)
          ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
            c.core) r)).1 := by
    intro w r
    change canonicalTerminal c.core
      (fibreQStarredWord hb c fallback w) r =
      (markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux
          c.core fallback w.1)
        (ForwardQMarkerCoverage.bulletForMarker c.core r)).1
    exact canonicalTerminal_actual_Q hb c fallback w r
  exact
    ForwardQMarkerTransportInterface.simple_pullback_smooth_of_canonical_marker_transport
      hb c fallback (canonicalTerminal c.core)
      (fun r => r ∈ B2)
      (ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv c.core)
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2)
      hpartition hcanonical color hsimple x y hxy

/-- A colouring simple with respect to the actual literal R
boundary extends to a TOTAL smooth colouring on the enlarged
mixed-product domain, with NO additional abstract canonical
marker-transport witness. The only additional inputs are
the genuine fixed R-indexed simplicity hypothesis and a
fallback colour for classes outside the starred domain. -/
theorem exists_total_relativeR_smooth_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (B2 : Set (ForwardQMarkerSmoothPartition.Marker c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (canonicalTerminal c.core)
        (fun r => r ∈ B2) color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2)
          x y → total x = total y) := by
  have hpartition :
      ∀ r : ForwardQMarkerSmoothPartition.Marker c.core,
        r ∈ B2 ↔
          ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
            c.core B2
            ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
              c.core) r) = false := by
    intro r
    change r ∈ B2 ↔
      ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2
        (ForwardQMarkerCoverage.bulletForMarker c.core r) = false
    exact
      (ForwardQMarkerSmoothPartition.gamma2_iff_B2 c.core B2 r).symm
  have hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback)
        (r : ForwardQMarkerSmoothPartition.Marker c.core),
        canonicalTerminal c.core
          (fibreQStarredWord hb c fallback w) r =
        (markedProjection c.core
          (ForwardQEnlargedConstantWords.eraseAux
            c.core fallback w.1)
          ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv
            c.core) r)).1 := by
    intro w r
    change canonicalTerminal c.core
      (fibreQStarredWord hb c fallback w) r =
      (markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux
          c.core fallback w.1)
        (ForwardQMarkerCoverage.bulletForMarker c.core r)).1
    exact canonicalTerminal_actual_Q hb c fallback w r
  exact
    ForwardQMarkerTransportInterface.exists_total_smooth_pullback_of_canonical_marker_transport
      hb c fallback fallbackColor (canonicalTerminal c.core)
      (fun r => r ∈ B2)
      (ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv c.core)
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core B2)
      hpartition hcanonical color hsimple

end DualTree.ForwardQRelativeMarkerSelector
