import DualTree.ForwardQFinalEnlargedGoodTransfer
import DualTree.MixedGoodSmoothReducedRecord

/-!
# Source-faithful reduced-record transfer for corrected Lemma 27

The actual Definition-11 c-good property factors a mixed-product
colouring through all D₂ marked points AND the letters at those
points. The verified Definition-21 smoothness condition removes
the marked letter at every Γ₂ coordinate: reassign just that
genuine local variable, keeping all outside-cone letters fixed.

The previous module normalized ALL Γ₂ letters in the genuine
mixed-variable-word span. This file transports its reduced
record to supported same-complete-signature targets using their
already kernel-verified genuinely enlarged typed starred Q
preimages. Only all marked points and the Γ₁ observed letters
survive in the reduced target record. The target colours are
constant on its fibres, for a total Q pullback that is both
smooth and c-good on the local mixed-word span.

This is strictly weaker than full starred-span monochromaticity
and more informative than the earlier full bulletRecord transfer.
It does not establish a quantitative mixed Ramsey witness,
the published reverse-lex W_* convention, or the full induction.
-/

namespace DualTree.ForwardQFinalEnlargedReducedGoodTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQModelBoundaryTransport
open ForwardQFinalTargetObservation
open ForwardQFinalEnlargedPairwiseTransfer
open ForwardQFinalEnlargedGoodTransfer

/-- The mathematically relevant normalized residual target
record for the corrected Γ₁/Γ₂ split: every actual selected
D₂ marked point, and a letter only at the Γ₁ coordinates.
No arbitrary choice of a colour or unstarred input is added. -/
noncomputable def reducedTargetBulletRecord
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    MixedProduct.BulletIndex (kind g.core) →
      (BoundedNode b (k - (m + 1)) ×
        Option (Sum α (Fin (m + 1)))) :=
  fun i =>
    let r := targetBulletRecord hb g f fallback hα O hTarget i
    (r.1, if gamma1 i then some r.2 else none)

/-- For a genuinely enlarged local mixed-word subspace on
which the total Q colouring is c-good, and a global
Γ₁/Γ₂ smooth total extension, any two eligible corrected
target observations with the same REDUCED bullet record
have identical colours.

This condition mentions no marked Γ₂ letters; the
verified real variable reassignment/normalization proves
those letters are irrelevant under smoothness. -/
theorem eligible_target_colors_eq_of_reduced_record
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput
      g.core → γ)
    (gamma1 : MixedProduct.BulletIndex (kind g.core) → Bool)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 =
        color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)))
    (hsmooth : ∀ x y : ForwardQEnlargedConstantWords.EnlargedInput
      g.core,
      MixedProduct.SmoothRelated gamma1 x y →
        total x = total y)
    (hgood : MixedProduct.Good total f)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : EligibleEnlargedTarget hb g f fallback O)
    (hP : EligibleEnlargedTarget hb g f fallback P)
    (hrec : reducedTargetBulletRecord hb g f fallback hα
      gamma1 O hO =
      reducedTargetBulletRecord hb g f fallback hα
      gamma1 P hP) :
    color (observe O) = color (observe P) := by
  let x := chosenStarredPreimage hb g f fallback hα O hO
  let y := chosenStarredPreimage hb g f fallback hα P hP
  have hx : x.1 ∈ f.span :=
    chosenStarredPreimage_mem_span hb g f fallback hα O hO
  have hy : y.1 ∈ f.span :=
    chosenStarredPreimage_mem_span hb g f fallback hα P hP
  have hpoints :
      ∀ i : MixedProduct.BulletIndex (kind g.core),
        x.1.bulletPoint i = y.1.bulletPoint i := by
    intro i
    have h := congrFun hrec i
    exact congrArg Prod.fst h
  have hgamma1 :
      ∀ i : MixedProduct.BulletIndex (kind g.core),
        gamma1 i = true →
        x.1.words i.1 (x.1.bulletPoint i) =
          y.1.words i.1 (y.1.bulletPoint i) := by
    intro i hi
    have h := congrArg Prod.snd (congrFun hrec i)
    change (if gamma1 i then
        some ((targetBulletRecord hb g f fallback hα O hO i).2)
        else none) =
      (if gamma1 i then
        some ((targetBulletRecord hb g f fallback hα P hP i).2)
        else none) at h
    rw [hi] at h
    have hvalue : (targetBulletRecord hb g f fallback hα O hO i).2 =
        (targetBulletRecord hb g f fallback hα P hP i).2 :=
      Option.some.inj h
    exact hvalue
  have hxy : total x.1 = total y.1 :=
    MixedProduct.good_smooth_color_eq_of_reduced_bullet_record
      f total gamma1 hgood hsmooth (Sum.inl fallback)
      x.1 y.1 hx hy hpoints hgamma1
  calc
    color (observe O) =
      color (observe
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback x)) :=
      congrArg color
        (chosenStarredPreimage_observe_eq
          hb g f fallback hα O hO).symm
    _ = total x.1 := (hagree x).symm
    _ = total y.1 := hxy
    _ = color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback y)) := hagree y
    _ = color (observe P) :=
      congrArg color
        (chosenStarredPreimage_observe_eq
          hb g f fallback hα P hP)

/-- Full conditional source-facing target transfer with the
TRUE reduced Γ₁/Γ₂ D₂ record. The intrinsic-root all-U simple
hypothesis supplies a total smooth pullback, and c-goodness
on any later genuinely enlarged local mixed word suffices to
make eligible target colours factor through their reduced
record (all points, only Γ₁ letters).

The quantitative existence of a suitable c-good local word,
the further removal of Γ₁ letters or Γ₂ points, the published
canonical selector and printed reverse-lex W_* still require
independent verified steps. -/
theorem exists_total_smooth_with_reduced_good_target_transfer
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (fallbackColor : γ)
    (B2 : Set (ModelA g.core))
    (color : Observation b n α → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        g
        (ForwardSemiCompleteCanonicalRoot.intrinsicModelPoint hb g.core)
        (fun a => a ∈ B2)
        (fun U => color (observe U))) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput
        g.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback,
        total w.1 =
          color (observe
            (ForwardQAmbientFibreLegalWord.fibreQStarredWord
              hb g fallback w))) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput
          g.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
            g.core (markerB2OfModelA hb g.core B2)) x y →
        total x = total y) ∧
      (∀ (q : Nat)
          (f : LocalMixedWord g.core q (Sum α (Fin (m + 1)))),
        MixedProduct.Good total f →
        ∀ O P : StarredSignature.StarredWord b n l α
            (SkewTree.forwardAuxB (b := b)),
          ∀ (hO : EligibleEnlargedTarget hb g f fallback O)
            (hP : EligibleEnlargedTarget hb g f fallback P),
            reducedTargetBulletRecord hb g f fallback hα
              (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
                g.core (markerB2OfModelA hb g.core B2)) O hO =
            reducedTargetBulletRecord hb g f fallback hα
              (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
                g.core (markerB2OfModelA hb g.core B2)) P hP →
            color (observe O) = color (observe P)) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteCanonicalRoot.exists_total_intrinsic_simple_Q_pullback
      hb g fallback fallbackColor B2
        (fun U => color (observe U)) hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hgood O P hO hP hrecord
  exact eligible_target_colors_eq_of_reduced_record
    hb g f fallback hα color total
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 g.core
        (markerB2OfModelA hb g.core B2))
      hagree hsmooth hgood O P hO hP hrecord

end DualTree.ForwardQFinalEnlargedReducedGoodTransfer
