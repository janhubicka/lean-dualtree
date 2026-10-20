import DualTree.ForwardQFinalCoherentLocalInput
import DualTree.ForwardQFinalExactOutputWord

/-!
# A coherent local mixed-span input matches the complete Q output word

A genuine original mixed-product point with admissible D1/D2 markers
can be relettered using one enlarged letter per actual component
variable root. The previous lemmas prove that this input belongs
to the enlarged local mixed-word span and that it decodes correctly
at each P_i(z). The full-signature early-root equality and the
verified late-unsafe fallback then imply exact Q/O word-symbol
agreement at ALL original homogeneous positions.

No Q-starred-tree or target-terminal equality is asserted: the
input's legal D2 markers are inherited from the supplied base point,
and must still be chosen to reconstruct O.tree.
-/

namespace DualTree.ForwardQFinalCoherentWordPreimage

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalCoherentLocalInput
open ForwardQFinalMixedAlphabetSpan

/-- The true coherent enlarged mixed-product input produces EXACTLY
the requested output dependent word on the whole original ambient
homogeneous tree, after the canonical same-root variable reindexing.

It uses a real local variable-fibre assignment, not an independent
letter for each projected coordinate. -/
theorem coherentInput_matches_full_Q_word
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
    (base : MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length
      α (kind g.core))
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (coherentInput hb g f O cutO H fallback base) s) =
      O.word.word s := by
  let w := coherentInput hb g f O cutO H fallback base
  have hlate :
      ∀ u : g.ambient.Vars,
        ¬ ForwardAux u.1.1 g.core.cut →
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w u.1) = O.word.word u.1 := by
    intro u hafter
    cases hs : ForwardQFinalSafeAddressLookup.safeAddress
        g.core u.1.1 with
    | none =>
        exact ForwardQFinalExactOutputWord.actual_Q_matches_output_on_unsafe_late_root
          hb g f fallback O cutO H hα hspan w u hafter hs
    | some a =>
        rcases a with ⟨i,z⟩
        have hpoint :
            u.1 = ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i z := by
          apply Subtype.ext
          change u.1.1 =
            (ForwardQFinalRefinementRoots.projected g.core ⟨i,z⟩).1
          exact (ForwardQFinalSafeAddressLookup.safeAddress_spec
            g.core u.1.1 ⟨i,z⟩ hs).symm
        rw [hpoint]
        exact coherentInput_Q_matches_output_at_projected
          hb g f fallback O cutO H hα hspan base i z
  exact ForwardQFinalExactWordReduction.actual_Q_word_eq_of_late_root_agreement
    hb g f fallback O cutO H hα hspan w hlate s

/-- Given an ACTUAL base mixed-product point in the local Ramsey span
with a legal corrected D2-starred marker order, a witness exists in
the enlarged mixed-product span with exactly those markers and with
the requested output's ENTIRE dependent word function.

This is a precise conditional word-level surjectivity assertion; the
base marker choice does NOT necessarily reconstruct the O.tree. -/
theorem exists_coherent_enlarged_starred_word_preimage
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
    (base : MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length
      α (kind g.core))
    (hbase : base ∈ f.span)
    (hstar : ForwardQActualStarredSpace.IsStarred g.core base) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      w ∈ (mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span ∧
      ForwardQActualStarredSpace.IsStarred g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w) ∧
      ∀ s : BoundedNode b n,
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s) = O.word.word s := by
  refine ⟨coherentInput hb g f O cutO H fallback base,
    coherentInput_mem_mixed_span hb g f O cutO H fallback base hbase,
    coherentInput_preserves_starred hb g f O cutO H fallback base hstar,
    ?_⟩
  intro s
  exact coherentInput_matches_full_Q_word
    hb g f fallback O cutO H hα hspan base s

end DualTree.ForwardQFinalCoherentWordPreimage
