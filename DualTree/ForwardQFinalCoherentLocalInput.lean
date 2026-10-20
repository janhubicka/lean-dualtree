import DualTree.ForwardQFinalLocalOutputFibres
import DualTree.ForwardQFinalOutputProjectedEncoder

/-!
# Coherent enlarged local input in the genuine mixed-product Ramsey span

Rather than encoding the output at each projected coordinate
independently, encode it only at each actual local variable root of
the mixed Ramsey word. Use that *same* enlarged letter throughout
its component-variable fibre. Original local constants retain their
original letters.

The two-letter output span hypothesis makes those root choices
decode to O at every projected coordinate, because the literal final
interpolated ambient word is uniform on component-variable fibres.

Marker legality is inherited from the original mixed-product base
point, not inferred from any unspecified choice of D2 points.

This does NOT yet prove that the resulting starred Q object equals O:
the precise target D2 terminals must still be reconstructed.
-/

namespace DualTree.ForwardQFinalCoherentLocalInput

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalOutputProjectedEncoder
open ForwardQFinalMixedAlphabetSpan

/-- One REAL enlarged-alphabet letter per actual local variable.
It is chosen at the canonical projected image of that variable's
ROOT and reused at all its occurrences in the local component word.
Both D1 and D2 points are copied from the given mixed-product point. -/
noncomputable def coherentInput
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length
      α (kind g.core)) :
    ForwardQEnlargedConstantWords.EnlargedInput g.core :=
  inputOfComponentChoices f
    (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))
    base
    (fun i v =>
      encodeProjectedOutputSymbol hb g O cutO H fallback i v.1)

/-- The coherent local enlarged-alphabet input belongs to the
ACTUAL span of the lifted mixed-product variable word, provided its
unchanged D1/D2 markers came from a legal point of the original span.
This assertion would be false for arbitrary independent letters. -/
theorem coherentInput_mem_mixed_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length
      α (kind g.core))
    (hbase : base ∈ f.span) :
    coherentInput hb g f O cutO H fallback base ∈
      (mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span :=
  inputOfComponentChoices_mem_span f
    (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))
    base hbase
    (fun i v =>
      encodeProjectedOutputSymbol hb g O cutO H fallback i v.1)

/-- The corrected D2-starred condition is preserved literally:
only ordinary coordinate letters were replaced, not marked points. -/
theorem coherentInput_preserves_starred
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length
      α (kind g.core))
    (hstar : ForwardQActualStarredSpace.IsStarred g.core base) :
    ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (coherentInput hb g f O cutO H fallback base)) :=
  hstar

/-- The ACTUAL corrected fibrewise Q symbol from the COHERENT
local mixed-product input equals O at every true P_i(z), after
canonical transport of dependent old/output variable names.

On a local constant, O preserves that letter by span inclusion.
On a local variable, the same selected enlarged letter is used
at z and at the variable root; O's symbols agree there by the
verified projected local-fibre uniformity. -/
theorem coherentInput_Q_matches_output_at_projected
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
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (coherentInput hb g f O cutO H fallback base)
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) := by
  let w := coherentInput hb g f O cutO H fallback base
  let e := sourceOutputVarsEquiv hb g O cutO H
  let p := ForwardQActualCoordinateWord.projectedBounded
    g.core g.T_bounded i z
  have hnode :
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (ForwardQActualCoordinateWord.projectLocal g.core i z).1
        (ForwardQActualCoordinateWord.projectLocal g.core i z).2).1 = p := by
    apply Subtype.ext
    rfl
  have hQ :=
    ForwardQAmbientFibreSymbol.fibreQ_projected_root
      g fallback w i z
  rw [hnode] at hQ
  cases hz : (f.vector.components i).word z with
  | inl a =>
      have hw : w.words i z = Sum.inl a := by
        simp [w, coherentInput, inputOfComponentChoices, hz]
      have hsymbol :
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w p = Sum.inl a := by
        rw [hw] at hQ
        simpa using hQ
      have hO : O.word.word p = Sum.inl a :=
        ForwardQFinalLocalOutputFibres.output_preserves_local_component_constant
          g f fallback O hα hspan i z a hz
      simpa [hsymbol, hO]
  | inr v =>
      have hw :
          w.words i z =
            encodeProjectedOutputSymbol hb g O cutO H fallback i v.1 := by
        simp [w, coherentInput, inputOfComponentChoices, hz]
      rw [hw] at hQ
      have hroot :=
        decoded_encoded_projected_output_symbol
          hb g O cutO H fallback i v.1
      have hO :=
        ForwardQFinalLocalOutputFibres.output_constant_on_local_variable_fibre
          g f fallback O hα hspan i v z hz
      calc
        Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w p) =
          Sum.map id e
            (match encodeProjectedOutputSymbol
              hb g O cutO H fallback i v.1 with
              | Sum.inl a => (Sum.inl a : Sum α g.core.source.word.Vars)
              | Sum.inr j =>
                  ForwardQVisibleAncestorDecoder.decodeAux
                    g.core fallback i j) :=
          congrArg (Sum.map id e) hQ
        _ = O.word.word
              (ForwardQActualCoordinateWord.projectedBounded
                g.core g.T_bounded i v.1) := hroot
        _ = O.word.word p := hO.symm

end DualTree.ForwardQFinalCoherentLocalInput
