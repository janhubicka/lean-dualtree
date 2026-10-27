import DualTree.ForwardQFinalEnlargedTargetD2Order
import DualTree.ForwardQFinalPairwiseTransfer

/-!
# Corollary-22-style pairwise colouring transfer for GENUINE enlarged words

The original conditional pairwise transfer theorem in
ForwardQFinalPairwiseTransfer dealt only with an α-valued local
mixed word whose constants were lifted to α ⊕ Fin(m+1).
That is not the local alphabet used by Corollary 22.

The full genuinely enlarged target preimage is now established for
f : LocalMixedWord c q (α ⊕ Fin(m+1)), including any FIXED auxiliary
constants, with the exact corrected starred D₂ condition deduced
from the target's skewness, and with equality of full rooted
tree-and-word observations.

It follows that pairwise monochromaticity on the STARRED portion
of the ACTUAL f.span transfers to the entire eligible class of
supported same-complete-signature targets in the genuine enlarged
f' span. No original-alphabet lifting, named common colour,
extra D₂-order assumption or unrestricted independent-root
reverse-coverage assumption survives.

The intrinsic canonical selector supplies an already verified
TOTAL SMOOTH pullback colouring whenever its full-ambient
simplicity hypothesis holds. Combining the two statements
reduces the corrected Lemma 27 colour step to the existence
of a smooth mixed-product Ramsey witness over the genuine
enlarged alphabet, with quantitative bounds and the corrected
forward-starred domain.

This is a CONDITIONAL Ramsey transfer. In particular it does not
establish the printed Corollary 22, which has its own audited
low-height obstruction, nor identify the original reverse-lex
starred domain with the repaired forward-lex domain.
-/

namespace DualTree.ForwardQFinalEnlargedPairwiseTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetObservation
open ForwardQModelBoundaryTransport

/-- The exact target family genuinely covered by a local
enlarged-alphabet mixed Ramsey word and the new ambient f'.
Every eligible O has the same corrected COMPLETE signature as
the source, its entire evaluated word span refines the actual
enlarged f', and its tree lies in the rank-filtered final support. -/
def EligibleEnlargedTarget
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  ∃ cutO : Node b,
    ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO ∧
    O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span ∧
    (∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))

/-- Every exactly eligible target admits a GENUINE enlarged
corrected starred mixed-span Q preimage having the same complete
representation-independent observable. Unlike the prior α-only
theorem, this does NOT require replacing fixed auxiliary symbols
by original-alphabet constants. -/
theorem eligible_enlarged_target_has_observation_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleEnlargedTarget hb g f fallback O) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  obtain ⟨cutO, H, hspan, hSupport⟩ := hTarget
  exact
    ForwardQFinalEnlargedTargetD2Order.exists_typed_enlarged_target_observation_preimage
      hb g f fallback O cutO H hα hspan hSupport

/-- The exact COROLLARY-22-SHAPED transfer: if a total
enlarged-product colouring agrees with the observable Q
pullback on actual starred inputs and is pairwise constant on
the STARRED portion of the genuine β-valued local mixed span,
then any two eligible corrected target O/P have equal colour.

Nothing is asked about the unstarred f.span; there is no chosen
common colour or nonempty-starred-span premise. -/
theorem eligible_enlarged_targets_pairwise_monochromatic
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
        color (observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w)))
    (hmono : ∀ x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      x.1 ∈ f.span → y.1 ∈ f.span →
      total x.1 = total y.1)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : EligibleEnlargedTarget hb g f fallback O)
    (hP : EligibleEnlargedTarget hb g f fallback P) :
    color (observe O) = color (observe P) := by
  obtain ⟨w, hw, hobsW⟩ :=
    eligible_enlarged_target_has_observation_preimage
      hb g f fallback hα O hO
  obtain ⟨z, hz, hobsZ⟩ :=
    eligible_enlarged_target_has_observation_preimage
      hb g f fallback hα P hP
  calc
    color (observe O) =
        color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)) := congrArg color hobsW.symm
    _ = total w.1 := (hagree w).symm
    _ = total z.1 := hmono w z hw hz
    _ = color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback z)) := hagree z
    _ = color (observe P) := congrArg color hobsZ

/-- The existing intrinsic-root canonical selector and
ALL-U simplicity criterion give a total SMOOTH Q pullback
colouring. Together with the new unconditional enlarged
target preimage, a single genuinely enlarged local mixed word
that is pairwise monochromatic on its STARRED span makes every
eligible fixed-complete-signature target monochromatic.

The existence of such a word, the precise quantitative mixed
Ramsey bounds, and the identification of printed Definition 24
and reverse-lex W_* are intentionally left OUTSIDE the theorem. -/
theorem exists_total_smooth_with_enlarged_pairwise_target_transfer
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
          color (observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w))) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput g.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 g.core
            (markerB2OfModelA hb g.core B2)) x y →
        total x = total y) ∧
      (∀ (q : Nat)
          (f : LocalMixedWord g.core q (Sum α (Fin (m + 1)))),
        (∀ x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback,
          x.1 ∈ f.span → y.1 ∈ f.span →
          total x.1 = total y.1) →
        ∀ O P : StarredSignature.StarredWord b n l α
            (SkewTree.forwardAuxB (b := b)),
          EligibleEnlargedTarget hb g f fallback O →
          EligibleEnlargedTarget hb g f fallback P →
          color (observe O) = color (observe P)) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteCanonicalRoot.exists_total_intrinsic_simple_Q_pullback
      hb g fallback fallbackColor B2
        (fun U => color (observe U)) hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hmono O P hO hP
  exact eligible_enlarged_targets_pairwise_monochromatic
    hb g f fallback hα color total hagree hmono O P hO hP

end DualTree.ForwardQFinalEnlargedPairwiseTransfer
