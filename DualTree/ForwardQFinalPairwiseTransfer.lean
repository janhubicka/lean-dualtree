import DualTree.ForwardQFinalColorTransfer

/-!
# Pairwise Corollary-22-style transfer for the corrected Lemma 27

Corollary 22 does NOT provide monochromaticity on the unrestricted
mixed-product span: it asserts that its STARRED portion is
monochromatic. Moreover this assertion is naturally pairwise, without
choosing a distinguished colour in advance.

The corrected target preimage now provides an actual starred witness
inside the lifted mixed-product span for every eligible same-signature
target, up to equality of complete root-labelled observations.
Consequently pairwise homogeneity of the starred mixed span
transports to pairwise homogeneity of all eligible targets.

This file combines that transport with the already verified total
smooth colouring extension for intrinsic-canonical-simple colourings.
The only remaining combinatorial hypothesis is the precise pairwise
starred-span conclusion of the corrected mixed Ramsey/Corollary-22
step. Its existence and numerical bounds remain unverified here.

The printed reverse-lex W_* domain and arbitrary dependence of a
colouring on tree list order are not implicitly identified with the
globally forward-corrected starred observation model.
-/

namespace DualTree.ForwardQFinalPairwiseTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetObservation
open ForwardQModelBoundaryTransport

/-- The EXACT target class covered by the current corrected Q
preimage, relative to a fixed source frame and a genuine chosen
post-Ramsey local mixed word f. The cut is included in the
complete corrected signature, and the final support restriction
is the actual rank-filtered one.

The definition does not accidentally demand that O range over
the WHOLE independently evaluated final-word span. -/
def EligibleTarget
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  ∃ cutO : Node b,
    ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO ∧
    O.word.span ⊆
      (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun a : α => a) fallback).span ∧
    (∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))

/-- The exact target eligibility predicate supplies an actual
corrected starred Q witness in the genuine lifted local span,
with literal equality of normalized full rooted observations.
No arbitrary choice of a final-root assignment is required. -/
theorem eligible_target_has_Q_observation_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTarget : EligibleTarget hb g f fallback O) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  obtain ⟨cutO, H, hspan, hSupport⟩ := hTarget
  exact exists_starred_Q_observation_preimage
    hb g f fallback O cutO H hα hspan hSupport
    (fun _ => fallback)

/-- PAIRWISE source-faithful transfer: any two eligible starred
targets have the SAME observable colour if the total Q pullback
agrees with the observed Q colouring and is monochromatic on
the STARRED portion of the real lifted local mixed-word span.

This does NOT demand full-span monochromaticity or a named common
colour. In particular it matches the quantifier pattern of the
paper's Corollary 22, unlike the stronger scalar-colour hypothesis
isolated for convenience in the previous module. -/
theorem eligible_targets_pairwise_monochromatic
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
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
      x.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
      y.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
      total x.1 = total y.1)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : EligibleTarget hb g f fallback O)
    (hP : EligibleTarget hb g f fallback P) :
    color (observe O) = color (observe P) := by
  obtain ⟨w, hw, hobsW⟩ :=
    eligible_target_has_Q_observation_preimage
      hb g f fallback hα O hO
  obtain ⟨z, hz, hobsZ⟩ :=
    eligible_target_has_Q_observation_preimage
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

/-- An intrinsic-canonical-simple colouring, formulated on
actual combinatorial tree-and-rooted-word observations, induces
a total SMOOTH mixed-product colouring. For EVERY later local
mixed word f whose STARRED span is pairwise monochromatic
under that total colouring, the entire exact eligible
fixed-signature target class is also monochromatic.

This isolates precisely the Corollary-22 Ramsey input and
removes a spurious nonemptiness/named-colour requirement.
The printed canonical selector, printed W_* and quantitative
existence of f are separate obligations. -/
theorem exists_total_smooth_with_pairwise_target_transfer
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
      (∀ (q : Nat) (f : LocalMixedWord g.core q α),
        (∀ x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback,
          x.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
            (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
          y.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
            (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span →
          total x.1 = total y.1) →
        ∀ O P : StarredSignature.StarredWord b n l α
            (SkewTree.forwardAuxB (b := b)),
          EligibleTarget hb g f fallback O →
          EligibleTarget hb g f fallback P →
          color (observe O) = color (observe P)) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteCanonicalRoot.exists_total_intrinsic_simple_Q_pullback
      hb g fallback fallbackColor B2
        (fun U => color (observe U)) hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hmono O P hO hP
  exact eligible_targets_pairwise_monochromatic
    hb g f fallback hα color total hagree hmono O P hO hP

end DualTree.ForwardQFinalPairwiseTransfer
