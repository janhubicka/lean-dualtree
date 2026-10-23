import DualTree.ForwardQFinalTargetObservation
import DualTree.ForwardSemiCompleteCanonicalRoot

/-!
# Conditional monochromatic transfer for the corrected Lemma 27 Q

We now have a target preimage as an ACTUAL corrected starred Q word in
the alphabet-lifted mixed-product span with exactly the same finite
tree support and complete rooted symbol function, independent of
list enumeration and dependent variable-name subtype proofs.

A smooth colouring of the total enlarged mixed product can therefore
be transported back to ALL supported same-signature targets provided
a local mixed Ramsey variable word f is monochromatic for that
colouring. The proof applies the exact target preimage, not a
fictional coverage of all unrestricted evaluations in span(f').

This module also combines the already checked intrinsic-root
Definition-24-style simplicity-to-smoothness construction with the
new target transfer. It isolates the ONE unproved combinatorial input
as a genuine monochromaticity hypothesis on the lifted local
mixed-product span; it does not assume that a matching mixed Ramsey
word always exists.

Everything is for the corrected forward auxiliary order, and the
colouring is a function of the genuine combinatorial observation
(tree vertex set plus whole root-labelled word), not a function of
arbitrary list order or dependent subtype proof representation.
-/

namespace DualTree.ForwardQFinalColorTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetObservation
open ForwardQModelBoundaryTransport

/-- A total enlarged mixed-product colouring that agrees with the
observed corrected Q colouring on starred inputs, and is constant
on the ENTIRE real lifted span of a chosen local mixed word f,
is constant on all supported same-complete-signature targets in
the constructed final support/refinement span.

This theorem uses NO extra D₂ ordering or independent final-root
assignment assumption; the fallback letter supplies one fixed
assignment required only internally by the target preimage proof. -/
theorem target_monochromatic_of_homogeneous_lifted_span
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (color : Observation b n α → γ)
    (total : ForwardQEnlargedConstantWords.EnlargedInput
      g.core → γ)
    (κ : γ)
    (hagree :
      ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
        total w.1 =
          color (observe
            (ForwardQAmbientFibreLegalWord.fibreQStarredWord
              hb g fallback w)))
    (hmono :
      ∀ x : ForwardQEnlargedConstantWords.EnlargedInput g.core,
        x ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
          (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
        total x = κ)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) :
    color (observe O) = κ := by
  obtain ⟨w, hwspan, hobs⟩ :=
    exists_starred_Q_observation_preimage
      hb g f fallback O cutO H hα hspan hSupport
      (fun _ => fallback)
  calc
    color (observe O) =
        color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w)) := congrArg color hobs.symm
    _ = total w.1 := (hagree w).symm
    _ = κ := hmono w.1 hwspan

/-- The already verified intrinsic canonical selector produces
a TOTAL smooth enlarged mixed-product colouring from the
source-facing, ALL-U simplicity predicate. Combining that with
the new observation-level preimage proves the exact conditional
target-colouring conclusion for ANY later local mixed Ramsey
word f on which this total colouring is monochromatic.

The existence of such an f and its numerical Ramsey parameters
remain an explicit, separately testable obligation. We also do
not identify this intrinsic selector with the printed undefined
semi-complete-tree selector I_U without further source alignment. -/
theorem exists_total_smooth_with_conditional_target_transfer
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
        total w.1 = color (observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w))) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput
          g.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2
            g.core (markerB2OfModelA hb g.core B2)) x y →
        total x = total y) ∧
      (∀ (q : Nat) (f : LocalMixedWord g.core q α) (κ : γ),
        (∀ x : ForwardQEnlargedConstantWords.EnlargedInput
            g.core,
          x ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
            (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
          total x = κ) →
        ∀ (O : StarredSignature.StarredWord b n l α
              (SkewTree.forwardAuxB (b := b)))
          (cutO : Node b)
          (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
            hb g O cutO),
          O.word.span ⊆
            (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
              g f (fun a : α => a) fallback).span →
          (∀ t : Node b, t ∈ O.tree →
            t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
              g.core f (m + q)) →
          color (observe O) = κ) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteCanonicalRoot.exists_total_intrinsic_simple_Q_pullback
      hb g fallback fallbackColor B2
        (fun U => color (observe U)) hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f κ hmono O cutO H hspan hSupport
  exact target_monochromatic_of_homogeneous_lifted_span
    hb g f fallback color total κ hagree hmono
    O cutO H hα hspan hSupport

end DualTree.ForwardQFinalColorTransfer
