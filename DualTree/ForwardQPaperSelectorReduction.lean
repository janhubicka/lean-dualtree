import DualTree.ForwardQModelBoundaryTransport

/-!
# Only Q-local agreement with the published model-A selector is needed

The corrected forward Q has a verified canonical source-labelled
bijection A_l ≃ R ≃ D2, and for every actual Q(w) the source-relative
model-A observable equals its true projected D2 leaf.

The paper's Definition 24 simplicity hypothesis, however, is about
its OWN canonical selector I_U(a), evaluated on arbitrary starred
substructures U. It has not yet been proved equal to the fixed-source
relative selector on every U; asserting that globally would be stronger
than required by the Lemma 27 colouring pullback.

This file proves the exact weaker reduction: given ANY selector J_U(a)
and a colouring simple in the ORIGINAL J-based sense on the entire
ambient starred domain, smoothness of c ∘ Q requires equality
  J_(Q(w))(a) = I^R_(Q(w))(a)
ONLY on the images of the genuine corrected starred Q construction.

There is no hypothesis whatsoever about J_U on arbitrary U not in
the Q image. The source-relative marker/point identity and the
B2-to-Gamma2 partition are fully discharged by earlier verified
geometry. The same Q-local condition is sufficient for the TOTAL
smooth colouring extension on the whole enlarged mixed product.

This is a conditional reduction, NOT a proof of agreement for the
published I_U, or of the printed reverse-order mixed starred domain.
-/

namespace DualTree.ForwardQPaperSelectorReduction

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQModelBoundaryTransport

/-- Any chosen subset B2 of the actual first-l model boundary
corresponds EXACTLY to the Gamma2 indices obtained from the
source-determined A_l ≃ R ≃ D2 bijection. -/
theorem modelA_B2_gamma2_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (B2 : Set (ModelA c))
    (a : ModelA c) :
    a ∈ B2 ↔
      ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c
        (markerB2OfModelA hb c B2)
        ((modelAToD2 hb c) a) = false := by
  let r := (ForwardSourceBoundaryEquiv.modelBoundaryMarkerEquiv hb c) a
  have hmem :
      a ∈ B2 ↔ r ∈ markerB2OfModelA hb c B2 := by
    change a ∈ B2 ↔
      ((ForwardSourceBoundaryEquiv.modelBoundaryMarkerEquiv hb c).symm
        ((ForwardSourceBoundaryEquiv.modelBoundaryMarkerEquiv hb c) a)) ∈ B2
    simp only [Equiv.symm_apply_apply]
  have hpart :=
    (ForwardQMarkerSmoothPartition.gamma2_iff_B2 c
      (markerB2OfModelA hb c B2) r).symm
  have hidx :
      (modelAToD2 hb c) a =
        ForwardQMarkerCoverage.bulletForMarker c r :=
    modelAToD2_apply hb c a
  rw [hidx]
  exact hmem.trans hpart

/-- For any paper-style selector J on ALL starred U, simplicity
of a colouring with respect to J implies the corrected Q
pullback is smooth provided J agrees with the already verified
source-relative selector ONLY ON ACTUAL Q OUTPUTS.

This does not replace the arbitrary-U simplicity hypothesis
with the weaker relative predicate: the original J-simple
hypothesis is retained exactly. -/
theorem paper_simple_Q_pullback_smooth_of_local_agreement
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (paperPoint :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) →
        ModelA c.core → Node b)
    (B2 : Set (ModelA c.core))
    (color :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → γ)
    (hpaperSimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c paperPoint (fun a => a ∈ B2) color)
    (hQlocal :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : ModelA c.core),
        paperPoint (fibreQStarredWord hb c fallback w) a =
          canonicalModelATerminal hb c.core
            (fibreQStarredWord hb c fallback w) a)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2)) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  have hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : ModelA c.core),
        paperPoint (fibreQStarredWord hb c fallback w) a =
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback w.1)
            ((modelAToD2 hb c.core) a)).1 := by
    intro w a
    exact (hQlocal w a).trans
      (canonicalModelATerminal_actual_Q hb c fallback w a)
  exact
    ForwardQMarkerTransportInterface.simple_pullback_smooth_of_canonical_marker_transport
      hb c fallback paperPoint (fun a => a ∈ B2)
      (modelAToD2 hb c.core)
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2))
      (modelA_B2_gamma2_iff hb c.core B2)
      hcanonical color hpaperSimple x y hxy

/-- The SAME Q-local canonical-selector agreement is sufficient
for a TOTAL classwise smooth extension on the entire enlarged
mixed-product input space, not merely the starred Q image.
There is no need to compare the canonical selectors on all U. -/
theorem exists_total_paper_simple_Q_pullback_of_local_agreement
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (paperPoint :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) →
        ModelA c.core → Node b)
    (B2 : Set (ModelA c.core))
    (color :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → γ)
    (hpaperSimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c paperPoint (fun a => a ∈ B2) color)
    (hQlocal :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : ModelA c.core),
        paperPoint (fibreQStarredWord hb c fallback w) a =
          canonicalModelATerminal hb c.core
            (fibreQStarredWord hb c fallback w) a) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
            (markerB2OfModelA hb c.core B2))
          x y → total x = total y) := by
  have hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : ModelA c.core),
        paperPoint (fibreQStarredWord hb c fallback w) a =
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback w.1)
            ((modelAToD2 hb c.core) a)).1 := by
    intro w a
    exact (hQlocal w a).trans
      (canonicalModelATerminal_actual_Q hb c fallback w a)
  exact
    ForwardQMarkerTransportInterface.exists_total_smooth_pullback_of_canonical_marker_transport
      hb c fallback fallbackColor paperPoint (fun a => a ∈ B2)
      (modelAToD2 hb c.core)
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2))
      (modelA_B2_gamma2_iff hb c.core B2)
      hcanonical color hpaperSimple

end DualTree.ForwardQPaperSelectorReduction
