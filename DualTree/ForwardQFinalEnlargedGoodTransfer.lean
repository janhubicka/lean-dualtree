import DualTree.ForwardQFinalEnlargedPairwiseTransfer
import DualTree.MixedGood

/-!
# Transfer the ACTUAL Definition-11 c-good conclusion to target colours

The stronger hypothesis that the entire corrected starred part of
a genuine enlarged mixed-product subspace is MONOCHROMATIC has a
separate Corollary-22 obstruction. Definition 11's verified
mixed-product c-good property is a distinct, weaker conclusion:
the colour can depend on the marked D₂ points and the letters
observed at those points.

Now that the complete corrected target preimage is proved for
genuine enlarged local words, we can transfer THAT exact
c-good invariant to supported targets, without silently
strengthening c-goodness to monochromaticity.

Choose, for each genuinely eligible target O, a typed corrected
starred Q preimage in the true local mixed-word span, and retain
its bulletRecord as a finite target observation. Since this Q
preimage has exactly O's full root-labelled observation, any
c-good total pullback colouring is constant across targets whose
chosen bulletRecords coincide.

This is intentionally a factorization/canonization theorem,
not full target monochromaticity. Its remaining record equality
condition is explicit, not assumed to follow from merely
matching complete signatures. The existence of a quantitative
c-good local mixed word and identification of the printed
reverse-lex W_* remain separate.
-/

namespace DualTree.ForwardQFinalEnlargedGoodTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetObservation
open ForwardQFinalEnlargedPairwiseTransfer
open ForwardQModelBoundaryTransport

/-- A canonical CHOICE of the actual verified enlarged starred Q
preimage of an eligible target. All choices are made within the
true starred mixed-span fibre, with the entire root-labelled
observation matching the target O. -/
noncomputable def chosenStarredPreimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback :=
  Classical.choose
    (eligible_enlarged_target_has_observation_preimage
      hb g f fallback hα O hTarget)

/-- The selected preimage belongs to the REAL β-valued
post-Ramsey mixed span, not to the old α-only constant lift. -/
theorem chosenStarredPreimage_mem_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    (chosenStarredPreimage hb g f fallback hα O hTarget).1 ∈ f.span :=
  (Classical.choose_spec
    (eligible_enlarged_target_has_observation_preimage
      hb g f fallback hα O hTarget)).1

/-- The selected preimage reproduces the target's ENTIRE
combinatorial rooted observation, independent of arbitrary
finite tree list orders and root subtype proof terms. -/
theorem chosenStarredPreimage_observe_eq
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
      hb g fallback
      (chosenStarredPreimage hb g f fallback hα O hTarget)) =
    observe O :=
  (Classical.choose_spec
    (eligible_enlarged_target_has_observation_preimage
      hb g f fallback hα O hTarget)).2

/-- The honest residual observable left by the c-good
mixed-product Ramsey theorem: the whole tuple of actual marked
D₂ points and the enlarged word letter at each marked point,
chosen from the certified Q preimage of the target. -/
noncomputable def targetBulletRecord
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    MixedProduct.BulletIndex (kind g.core) →
      (BoundedNode b (k - (m + 1)) × Sum α (Fin (m + 1))) :=
  MixedProduct.bulletRecord
    (chosenStarredPreimage hb g f fallback hα O hTarget).1

/-- Definition 11's ACTUAL c-good hypothesis on the genuine
enlarged local variable word implies equality of the target
observation colours whenever their canonical target D₂ bullet
records agree.

No full starred-span monochromaticity is assumed. All target
support, complete signature and evaluated-span hypotheses
occur only through the exact eligible-target predicate. -/
theorem eligible_enlarged_target_colors_eq_of_good_record
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (color : Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput
      g.core → γ)
    (hagree : ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback,
      total w.1 =
        color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)))
    (hgood : MixedProduct.Good total f)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : EligibleEnlargedTarget hb g f fallback O)
    (hP : EligibleEnlargedTarget hb g f fallback P)
    (hrecord :
      targetBulletRecord hb g f fallback hα O hO =
      targetBulletRecord hb g f fallback hα P hP) :
    color (observe O) = color (observe P) := by
  let x := chosenStarredPreimage hb g f fallback hα O hO
  let y := chosenStarredPreimage hb g f fallback hα P hP
  have hx : x.1 ∈ f.span :=
    chosenStarredPreimage_mem_span hb g f fallback hα O hO
  have hy : y.1 ∈ f.span :=
    chosenStarredPreimage_mem_span hb g f fallback hα P hP
  have hrec : MixedProduct.bulletRecord x.1 =
      MixedProduct.bulletRecord y.1 := hrecord
  have hxy :
      total x.1 = total y.1 :=
    MixedProduct.color_eq_of_good_of_same_record
      hgood hx hy hrec
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

/-- Combining intrinsic-root all-U simplicity with the verified
smooth total Q pullback and the new genuinely enlarged c-good
target transfer, any later c-good enlarged local mixed word
produces a colouring of eligible corrected target words that
FACTORS THROUGH the explicit selected target bulletRecord.

This gives a usable conditional interface to the actual
Definition-11 mixed Ramsey canonization, rather than wrongly
requiring full starred-span monochromaticity. The residual
bulletRecord must still be eliminated or canonized by a
separate Ramsey/induction step; no false full Lemma 27
completion is claimed. -/
theorem exists_total_smooth_with_enlarged_good_record_transfer
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
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput g.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 g.core
            (markerB2OfModelA hb g.core B2)) x y →
        total x = total y) ∧
      (∀ (q : Nat)
          (f : LocalMixedWord g.core q (Sum α (Fin (m + 1)))),
        MixedProduct.Good total f →
        ∀ O P : StarredSignature.StarredWord b n l α
            (SkewTree.forwardAuxB (b := b)),
          ∀ (hO : EligibleEnlargedTarget hb g f fallback O)
            (hP : EligibleEnlargedTarget hb g f fallback P),
            targetBulletRecord hb g f fallback hα O hO =
            targetBulletRecord hb g f fallback hα P hP →
            color (observe O) = color (observe P)) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteCanonicalRoot.exists_total_intrinsic_simple_Q_pullback
      hb g fallback fallbackColor B2
        (fun U => color (observe U)) hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hgood O P hO hP hrecord
  exact eligible_enlarged_target_colors_eq_of_good_record
    hb g f fallback hα color total hagree hgood O P hO hP hrecord

end DualTree.ForwardQFinalEnlargedGoodTransfer
