import DualTree.ForwardQFinalTerminalSafety
import DualTree.ForwardQFinalInducedStarredPoint

/-!
# Coherent enlarged Q word preimage for positive local dimension

The previous exact full-word theorem was conditional on a legal
corrected-starred base point of the original mixed-product span.

That base point already exists for every q>0: the checked
ForwardQFinalInducedStarredPoint.inducedStarredInput uses the
intrinsic-rank-zero roots of the actual local components as its
D2 marker points. Vector completeness verifies the corrected
starred order, while its component words are genuine evaluations
of the local mixed product f.

Combining this constructor with the coherent enlarged-letter
construction removes the base-point existence hypothesis.
The resulting enlarged word lies in the lifted mixed Ramsey span,
satisfies the actual corrected starred input condition, and its
fibrewise Q symbols agree with O everywhere, under the earlier
same-signature and two-letter output-span hypotheses.

It DOES NOT show equality of the selected D2 terminals with
those of the PARTICULAR requested O.tree, and hence makes no
claim of object-valued Q surjectivity.
-/

namespace DualTree.ForwardQFinalPositiveQWordPreimage

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport

/-- The source-facing local mixed-product span has a point whose
ACTUAL corrected starred D2 condition holds whenever q>0.
This is a reusable consequence of the verified intrinsic-zero
D2-marker construction; no arbitrary marked points are assumed. -/
theorem exists_starred_base_in_mixed_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q) :
    ∃ base : ForwardSourceQTree.Input g.core,
      base ∈ f.span ∧
      ForwardQActualStarredSpace.IsStarred g.core base := by
  let σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α :=
    fun _ => fallback
  let baseStar :=
    ForwardQFinalInducedStarredPoint.inducedStarredInput
      g f fallback σ hq
  refine ⟨baseStar.1, ?_, baseStar.2⟩
  exact ForwardQFinalInducedStarredPoint.inducedStarredInput_mem_mixed_span
    g f fallback σ hq

/-- The enlarged mixed Ramsey span ALWAYS contains a corrected-starred
point whose ACTUAL fibrewise Q WORD equals the required target
dependent word (after the canonical old/output variable equivalence),
provided q>0 and the printed source/signature/span hypotheses hold.

No unspecified choice of D2 points is used: it comes from the
existing verified rank-zero marked-point selection theorem. -/
theorem exists_positive_q_coherent_word_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hq : 0 < q) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      w ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span ∧
      ForwardQActualStarredSpace.IsStarred g.core
        (ForwardQEnlargedConstantWords.eraseAux
          g.core fallback w) ∧
      ∀ s : BoundedNode b n,
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s) = O.word.word s := by
  obtain ⟨base, hspanBase, hstarBase⟩ :=
    exists_starred_base_in_mixed_span g f fallback hq
  exact ForwardQFinalCoherentWordPreimage.exists_coherent_enlarged_starred_word_preimage
    hb g f fallback O cutO H hα hspan base hspanBase hstarBase

end DualTree.ForwardQFinalPositiveQWordPreimage
