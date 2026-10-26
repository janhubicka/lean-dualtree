import DualTree.ForwardQFinalEnlargedWholeDomainEvaluation
import DualTree.ForwardQFinalFullSignatureRootTransport

/-!
# Target-symbol rigidity for the genuinely enlarged final word

The earlier exact starred target Q preimage used a local Ramsey word
over the original alphabet. The genuine Corollary-22 local word may
instead contain FIXED auxiliary symbols in α ⊕ Fin (m+1). These are
decoded through R_i into genuine retained OLD final variable roots.

Under the actual two-letter evaluated-span refinement O.word.span ⊆
span(f'_enlarged), we prove the relevant *symbolic* rigidity:

* the final word's symbol at P_i(z) is the genuine decoded local
  symbol, with NO incorrect α-only decoding;
* the whole target word is constant on a genuine local variable
  fibre, including the independent global projected root P_i(v);
* a fixed original constant of a local component is preserved by O;
* a fixed auxiliary constant j is sent in O to exactly the
  root-reindexed actual source decoder R_i(j). In particular when
  R_i(j) names an old source variable, the target is forced to
  name that same root, not an arbitrary constant.

These are missing components of the complete reverse target
Q-preimage proof for the *genuine enlarged* final f'. They do not
yet assert global target Q surjectivity, D₂-starred reconstruction
or equivalence with the printed reverse-lex starred domain.
-/

namespace DualTree.ForwardQFinalEnlargedTargetLocalFibres

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedLocalSymbols
open ForwardQFinalEnlargedProjectedEval
open ForwardQFinalFullSignatureRootTransport

/-- The genuine final word at the bounded projected P_i(z) is
exactly the decoded local enlarged symbol. This merely aligns
the two representations of the same original ambient T root. -/
theorem final_word_at_projected
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    (enlargedInterpolatedFinalWord g f fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
      enlargedLocalSymbol g f fallback i z := by
  have hnode :
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2).1 =
      ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z := by
    apply Subtype.ext
    rfl
  rw [← hnode]
  exact enlargedFinalWord_projected_root_symbol g f fallback i z

/-- One actual local component-variable fibre has exactly
the same genuine enlarged final-root symbol at all of its
occurrences, whether the variable is kept or the rank filter
excludes it. -/
theorem final_word_constant_on_local_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k-(m+1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    (enlargedInterpolatedFinalWord g f fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    (enlargedInterpolatedFinalWord g f fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i v.1) := by
  have hroot := (f.vector.components i).toVariableWord.atRoot v
  have hlocal :
      enlargedLocalSymbol g f fallback i z =
      enlargedLocalSymbol g f fallback i v.1 := by
    simp [enlargedLocalSymbol, hz, hroot]
  have hzFinal := final_word_at_projected g f fallback i z
  have hvFinal := final_word_at_projected g f fallback i v.1
  exact hzFinal.trans (hlocal.trans hvFinal.symm)

/-- A target refining the genuinely enlarged final word cannot
vary its *actual dependent variable-word symbol* along one local
component-variable fibre. This requires the two-letter hypothesis;
mere coincidence of one evaluation is not sufficient. -/
theorem output_constant_on_local_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (enlargedInterpolatedFinalWord g f fallback).span)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k-(m+1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i v.1) := by
  obtain ⟨ρ, hword⟩ :=
    (VariableWord.span_subset_iff_substitution hα
      (enlargedInterpolatedFinalWord g f fallback) O.word).1 hspan
  have hf := final_word_constant_on_local_variable_fibre
    g f fallback i v z hz
  calc
    O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
      SpanAudit.substitute
        (enlargedInterpolatedFinalWord g f fallback).word ρ
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) := congrFun hword _
    _ = SpanAudit.substitute
        (enlargedInterpolatedFinalWord g f fallback).word ρ
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i v.1) := by
            simp [SpanAudit.substitute, hf]
    _ = O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i v.1) := (congrFun hword _).symm

/-- A fixed original alphabet constant in a genuine enlarged
local Ramsey word remains the SAME constant in the actual
target O, under the required evaluated-span refinement. -/
theorem output_preserves_original_local_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (enlargedInterpolatedFinalWord g f fallback).span)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (a : α)
    (hz : (f.vector.components i).word z =
      Sum.inl (Sum.inl a)) :
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) = Sum.inl a := by
  have hf :
      (enlargedInterpolatedFinalWord g f fallback).word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) = Sum.inl a := by
    rw [final_word_at_projected]
    simp [enlargedLocalSymbol, hz]
    rfl
  exact SpanAudit.constant_preserved_of_span_subset hα
    (enlargedInterpolatedFinalWord g f fallback).word
    O.word.word hspan hf

/-- If a genuine enlarged local Ramsey word fixes an auxiliary
constant j, the target O's REAL dependent variable-word symbol
is exactly the same R_i(j) decoder symbol, under canonical
identification of the old source and target variables.

In the nontrivial case R_i(j) = old variable v, the enlarged
final word emits the old retained root of v. Its own atRoot
law and the target's evaluated-span inclusion force the target
to emit the corresponding old variable, not a constant. -/
theorem output_preserves_aux_local_constant
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (enlargedInterpolatedFinalWord g f fallback).span)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (j : Fin (m+1))
    (hz : (f.vector.components i).word z =
      Sum.inl (Sum.inr j)) :
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
      Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
        (ForwardQVisibleAncestorDecoder.decodeAux
          g.core fallback i j) := by
  let e := sourceOutputVarsEquiv hb g O cutO H
  have hfinal :
      (enlargedInterpolatedFinalWord g f fallback).word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
      decodeAuxIntoFinal g f fallback i j := by
    calc
      _ = enlargedLocalSymbol g f fallback i z :=
        final_word_at_projected g f fallback i z
      _ = decodeAuxIntoFinal g f fallback i j :=
        enlargedLocalSymbol_aux_constant g f fallback i z j hz
  cases hd : ForwardQVisibleAncestorDecoder.decodeAux
      g.core fallback i j with
  | inl a =>
      have hf :
          (enlargedInterpolatedFinalWord g f fallback).word
            (ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i z) = Sum.inl a := by
        have hAux :
            decodeAuxIntoFinal g f fallback i j = Sum.inl a := by
          simp [decodeAuxIntoFinal, hd]
        exact hfinal.trans hAux
      have ho := SpanAudit.constant_preserved_of_span_subset hα
        (enlargedInterpolatedFinalWord g f fallback).word
        O.word.word hspan hf
      simpa [hd] using ho
  | inr v =>
      let rv := ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
        g f v
      have hf :
          (enlargedInterpolatedFinalWord g f fallback).word
            (ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i z) = Sum.inr rv := by
        have hAux :
            decodeAuxIntoFinal g f fallback i j = Sum.inr rv := by
          simp [decodeAuxIntoFinal, hd, rv]
        exact hfinal.trans hAux
      have hr :
          (enlargedInterpolatedFinalWord g f fallback).word
            rv.1 = Sum.inr rv :=
        (enlargedInterpolatedFinalWord g f fallback).atRoot rv
      have ho : O.word.word
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i z) = O.word.word rv.1 :=
        SpanAudit.fibre_uniform_of_span_subset hα
          (enlargedInterpolatedFinalWord g f fallback).word
          O.word.word hspan hf hr
      have hrv : rv.1 = (e v).1 := by
        apply Subtype.ext
        calc
          rv.1.1 = v.1.1 :=
            oldSourceFinalRoot_underlying g f v
          _ = (e v).1.1 :=
            (congrArg Subtype.val
              (sourceOutputVarsEquiv_root hb g O cutO H v)).symm
      have hOroot : O.word.word rv.1 = Sum.inr (e v) := by
        rw [hrv]
        exact O.word.atRoot (e v)
      have hdecode :
          Sum.map id e
            (ForwardQVisibleAncestorDecoder.decodeAux
              g.core fallback i j) = Sum.inr (e v) := by
        rw [hd]
        rfl
      change O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
          Sum.map id e
            (ForwardQVisibleAncestorDecoder.decodeAux
              g.core fallback i j)
      exact ho.trans (hOroot.trans hdecode.symm)

end DualTree.ForwardQFinalEnlargedTargetLocalFibres
