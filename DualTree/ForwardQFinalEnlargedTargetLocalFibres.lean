import DualTree.ForwardQSourceRefinement
import DualTree.ForwardQFinalEnlargedWholeDomainEvaluation
import DualTree.ForwardQFinalFullSignatureRootTransport

/-!
# Target-symbol rigidity for the genuinely enlarged final word

The earlier exact starred target Q preimage used a local Ramsey word
over the original alphabet. The genuine Corollary-22 local word may
instead contain FIXED auxiliary symbols in α ⊕ Fin (m+1). These are
decoded through R_i into genuine retained OLD final variable roots.

Under explicit syntactic refinement of O by the enlarged final word,
we prove the relevant symbolic rigidity for every alphabet. The original
evaluated-span forms follow when the alphabet has two distinct letters:

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
component-variable fibre. The explicit syntactic refinement suffices
for every alphabet; coincidence of one evaluation would not. -/
theorem output_constant_on_local_variable_fibre_of_syntactic_refinement
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hRef : ForwardQSourceRefinement.SyntacticallyRefines O.word
      (enlargedInterpolatedFinalWord g f fallback))
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
  exact hRef.preserves_symbol_eq
    (final_word_constant_on_local_variable_fibre g f fallback i v z hz)

/-- Evaluated-span form. The two-letter assumption is used only to
recover the explicit syntactic refinement required by the general theorem. -/
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
  exact output_constant_on_local_variable_fibre_of_syntactic_refinement
    g f fallback O
    ((ForwardQSourceRefinement.syntacticallyRefines_iff_span_subset
        hα O.word (enlargedInterpolatedFinalWord g f fallback)).2 hspan) i v z hz

/-- A fixed original alphabet constant in a genuine enlarged
local Ramsey word remains the SAME constant in the actual
target O, under the explicit syntactic refinement. -/
theorem output_preserves_original_local_constant_of_syntactic_refinement
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hRef : ForwardQSourceRefinement.SyntacticallyRefines O.word
      (enlargedInterpolatedFinalWord g f fallback))
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
  exact hRef.preserves_constant hf

/-- Evaluated-span form. The two-letter assumption is used only to
recover the explicit syntactic refinement required by the general theorem. -/
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
  exact output_preserves_original_local_constant_of_syntactic_refinement
    g f fallback O
    ((ForwardQSourceRefinement.syntacticallyRefines_iff_span_subset
        hα O.word (enlargedInterpolatedFinalWord g f fallback)).2 hspan) i z a hz

/-- If a genuine enlarged local Ramsey word fixes an auxiliary
constant j, the target O's REAL dependent variable-word symbol
is exactly the same R_i(j) decoder symbol, under canonical
identification of the old source and target variables.

In the nontrivial case R_i(j) = old variable v, the enlarged
final word emits the old retained root of v. Its own atRoot
law and the target's syntactic refinement force the target
to emit the corresponding old variable, not a constant. -/
theorem output_preserves_aux_local_constant_of_syntactic_refinement
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
    (hRef : ForwardQSourceRefinement.SyntacticallyRefines O.word
      (enlargedInterpolatedFinalWord g f fallback))
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
      have ho := hRef.preserves_constant hf
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
        hRef.preserves_symbol_eq (hf.trans hr.symm)
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
      -- The preceding case split has already rewritten R_i(j)
      -- to Sum.inr v in the GOAL; do not try to rewrite it twice.
      simpa only [Sum.map_inr] using ho.trans hOroot

/-- Evaluated-span form. The two-letter assumption is used only to
recover the explicit syntactic refinement required by the general theorem. -/
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
  exact output_preserves_aux_local_constant_of_syntactic_refinement
    hb g f fallback O cutO H
    ((ForwardQSourceRefinement.syntacticallyRefines_iff_span_subset
        hα O.word (enlargedInterpolatedFinalWord g f fallback)).2 hspan) i z j hz


end DualTree.ForwardQFinalEnlargedTargetLocalFibres
