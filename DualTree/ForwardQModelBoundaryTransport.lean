import DualTree.ForwardSourceBoundaryEquiv
import DualTree.ForwardQRelativeMarkerSelector
import DualTree.ForwardQMarkerSmoothPartition

/-!
# Transport corrected source-relative simplicity from model A to R

The corrected source geometry now supplies an actual canonical
equivalence between the first-l homogeneous model boundary A
and the literal source first-exit marker set R.

We transport the existing R-relative terminal observable to
the model boundary A by this equivalence. For arbitrary starred
outputs U, this is a source-relative observable: it chooses an
output terminal above the FIXED source R marker if one exists.
For every genuine corrected Q output, the observable equals
the exact projected D2 point prescribed by the construction.

The previously proved R-relative simplicity/smoothness lemma
can therefore be restated for any B2 subset of the actual
homogeneous model A, with the corresponding D2 coordinates
obtained canonically by composing A≃R≃D2.

IMPORTANT: This does NOT by itself identify the observable
on arbitrary starred refinements with the published Definition
24 canonical embedding I_U(a). The simplicity assumption in
the final theorems is explicitly the source-relative model-A
predicate defined here, not an unverified equivalence with the
paper's independent canonical selector. Word/span consistency,
printed reverse-lex source-domain transport and Ramsey iteration
remain separate proof obligations.
-/

namespace DualTree.ForwardQModelBoundaryTransport

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardSourceBoundaryEquiv

/-- The first-l homogeneous model boundary, now an actual
source-facing subtype rather than an abstract marker type. -/
abbrev ModelA
    {b n l k m : Nat} {α : Type*}
    (_c : Frame b n l k m α) :=
  {a : Node b // ForwardModelBoundaryHeap.ModelBoundary l a}

/-- Canonical model boundary coordinates in the TRUE corrected
D2 family, through the checked equivalences A ≃ R ≃ D2. -/
noncomputable def modelAToD2
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    ModelA c ≃ MixedProduct.BulletIndex (kind c) :=
  (modelBoundaryMarkerEquiv hb c).trans
    (ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv c)

/-- The model coordinate is exactly the sorted bullet coordinate
of its literal source marker; the equivalence does not hide
an arbitrary permutation of D2. -/
theorem modelAToD2_apply
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : ModelA c) :
    (modelAToD2 hb c) a =
      ForwardQMarkerCoverage.bulletForMarker c
        ((modelBoundaryMarkerEquiv hb c) a) := by
  rfl

/-- A source-relative canonical terminal observable, indexed
by ACTUAL model A addresses. It is defined on every starred
output by first transporting A to the fixed source R marker.
It is not asserted to equal the printed I_U(a) on arbitrary U. -/
noncomputable def canonicalModelATerminal
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : ModelA c) : Node b :=
  ForwardQRelativeMarkerSelector.canonicalTerminal c U
    ((modelBoundaryMarkerEquiv hb c) a)

/-- For every actual corrected Q(w), the model-A terminal
observable is exactly the projected genuine D2 marker point.
This DISCHARGES the Q-specific geometric premise of the
abstract simplicity-to-smoothness interface for this selector. -/
theorem canonicalModelATerminal_actual_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : ModelA c.core) :
    canonicalModelATerminal hb c.core
      (fibreQStarredWord hb c fallback w) a =
      (markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux
          c.core fallback w.1)
        ((modelAToD2 hb c.core) a)).1 := by
  change ForwardQRelativeMarkerSelector.canonicalTerminal c.core
      (fibreQStarredWord hb c fallback w)
      ((modelBoundaryMarkerEquiv hb c.core) a) =
    (markedProjection c.core
      (ForwardQEnlargedConstantWords.eraseAux
        c.core fallback w.1)
      ((modelAToD2 hb c.core) a)).1
  rw [modelAToD2_apply hb c.core a]
  exact ForwardQRelativeMarkerSelector.canonicalTerminal_actual_Q
    hb c fallback w ((modelBoundaryMarkerEquiv hb c.core) a)

/-- Transport a B2 subset of canonical model A to the genuine
source-relative R marker set, without introducing coordinates
not corresponding to source boundary addresses. -/
noncomputable def markerB2OfModelA
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (B2 : Set (ModelA c)) :
    Set (ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout) :=
  {r | ((modelBoundaryMarkerEquiv hb c).symm r) ∈ B2}

/-- A colouring simple in the model-A source-relative
selector is also simple in the literal R-relative selector,
with B2 transported by the checked boundary equivalence. -/
theorem modelA_simple_to_relativeR_simple
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (canonicalModelATerminal hb c.core)
        (fun a => a ∈ B2) color) :
    ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
      c (ForwardQRelativeMarkerSelector.canonicalTerminal c.core)
      (fun r => r ∈ markerB2OfModelA hb c.core B2)
      color := by
  intro u v hu hv hinter hmarker houtside
  apply hsimple u v hu hv hinter
  · intro a ha
    have hr :
        ((modelBoundaryMarkerEquiv hb c.core) a) ∈
          markerB2OfModelA hb c.core B2 := by
      change
        ((modelBoundaryMarkerEquiv hb c.core).symm
          ((modelBoundaryMarkerEquiv hb c.core) a)) ∈ B2
      simpa only [Equiv.symm_apply_apply] using ha
    exact hmarker ((modelBoundaryMarkerEquiv hb c.core) a) hr
  · intro s houtA
    apply houtside s
    intro r hr
    have ha :
        ((modelBoundaryMarkerEquiv hb c.core).symm r) ∈ B2 := hr
    have hout :=
      houtA ((modelBoundaryMarkerEquiv hb c.core).symm r) ha
    change ¬ IsPrefix
      (ForwardQRelativeMarkerSelector.canonicalTerminal c.core u
        ((modelBoundaryMarkerEquiv hb c.core)
          ((modelBoundaryMarkerEquiv hb c.core).symm r))) s.1 at hout
    simpa only [Equiv.apply_symm_apply] using hout

/-- Smoothness of the actual corrected Q pullback for a
model-A-indexed source-relative simple colouring and an
arbitrary B2 subset of A. All D2 indices are transported
by the canonical A≃R≃D2 equivalence. -/
theorem modelA_simple_pullback_smooth
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (canonicalModelATerminal hb c.core)
        (fun a => a ∈ B2) color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2)) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  exact ForwardQRelativeMarkerSelector.relativeR_simple_pullback_smooth
    hb c fallback (markerB2OfModelA hb c.core B2)
    color (modelA_simple_to_relativeR_simple hb c B2 color hsimple)
    x y hxy

/-- The model-A source-relative simple pullback extends to a
TOTAL smooth colouring of the enlarged mixed product.
No independent abstract marker-transport assumption is needed. -/
theorem exists_total_modelA_smooth_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (canonicalModelATerminal hb c.core)
        (fun a => a ∈ B2) color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
            (markerB2OfModelA hb c.core B2))
          x y → total x = total y) := by
  exact ForwardQRelativeMarkerSelector.exists_total_relativeR_smooth_pullback
    hb c fallback fallbackColor
    (markerB2OfModelA hb c.core B2) color
    (modelA_simple_to_relativeR_simple hb c B2 color hsimple)

end DualTree.ForwardQModelBoundaryTransport
