import DualTree.ForwardQFinalEnlargedTargetProjectedWord
import DualTree.ForwardQFinalExactOutputWord

/-!
# Exact enlarged-alphabet target Q dependent word, on the ENTIRE tree

For a genuine post-Corollary-22 mixed variable word with constant
alphabet α ⊕ Fin(m+1), the coherent target input uses exactly the
requested D₂ terminal points and only uniform local variable
assignments. The previous lemma proves its actual Q decoder
matches O at every safe projected ambient T-root, including
fixed auxiliary local constants decoded as old variables.

Here the remaining original ambient-fibre cases are assembled:
early source roots by equality of COMPLETE corrected signatures;
unsafe late roots by the common literal fallback;
original ambient constants by span preservation; and arbitrary
occurrences in any original f-fibre by two-letter symbolic
uniformity. This proves exact equality of the ENTIRE dependent
variable-word function after the canonical root equivalence.

Combined with the separately verified generic exact Q node SET,
the genuine enlarged mixed Ramsey span therefore contains a
RAW Q input reconstructing both the entire target node set and
full rooted word. The only missing local condition for the
corrected starred-Q preimage is now the D₂-marked-tuple order
in the actual enlarged input; no such certificate is claimed
in this file. Printed reverse-lex W_* is still separate.
-/

namespace DualTree.ForwardQFinalEnlargedTargetWholeWord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalEnlargedTargetLocalFibres
open ForwardQFinalEnlargedTargetInput
open ForwardQFinalEnlargedTargetProjectedWord
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedWholeDomainEvaluation
open ForwardQFinalSafeAddressLookup

/-- Under the genuine enlarged final-word span hypothesis,
the target O has the correct fallback CONSTANT on every
unsafe post-cut original ambient f-variable root. -/
theorem output_unsafe_late_fallback
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (enlargedInterpolatedFinalWord g f fallback).span)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : safeAddress g.core u.1.1 = none) :
    O.word.word u.1 = Sum.inl fallback := by
  have hsub :
      enlargedGlobalRootSymbol g f fallback u = Sum.inl fallback :=
    enlargedGlobalRootSymbol_late_no_safe
      g f fallback u hafter hnone
  have hf :
      (enlargedInterpolatedFinalWord g f fallback).word u.1 =
        Sum.inl fallback := by
    change SpanAudit.substitute g.ambient.word
      (enlargedGlobalRootSymbol g f fallback) u.1 =
      Sum.inl fallback
    simp [SpanAudit.substitute,g.ambient.atRoot u,hsub]
  exact SpanAudit.constant_preserved_of_span_subset hα
    (enlargedInterpolatedFinalWord g f fallback).word
    O.word.word hspan hf

/-- The coherent target input reconstructs the REAL target's
dependent symbol at every genuine original ambient f-variable
root, including the cut, safe late roots and unsafe fallback. -/
theorem coherent_target_Q_matches_at_original_f_root
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
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (u : g.ambient.Vars) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (coherentTargetInput hb g f fallback O cutO H hSupport)
        u.1) = O.word.word u.1 := by
  let w := coherentTargetInput hb g f fallback O cutO H hSupport
  by_cases hbefore : ForwardAux u.1.1 g.core.cut
  · exact ForwardQFinalExactWordReduction.actual_Q_matches_output_on_early_root
      hb g O cutO H fallback w u hbefore
  · cases hsafe : safeAddress g.core u.1.1 with
    | none =>
        have hQ :
            ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
              w u.1 = Sum.inl fallback :=
          ForwardQFinalExactOutputWord.actual_Q_fallback_at_unsafe_late_root
            g fallback w u hbefore hsafe
        have hO : O.word.word u.1 = Sum.inl fallback :=
          output_unsafe_late_fallback
            g f fallback O hα hspan u hbefore hsafe
        simp [hQ,hO]
    | some addr =>
        rcases addr with ⟨i,z⟩
        have hpoint :
            u.1 = ForwardQActualCoordinateWord.projectedBounded
              g.core g.T_bounded i z := by
          apply Subtype.ext
          change u.1.1 = (projected g.core ⟨i,z⟩).1
          exact (safeAddress_spec
            g.core u.1.1 ⟨i,z⟩ hsafe).symm
        rw [hpoint]
        exact coherent_target_Q_matches_at_projected
          hb g f fallback O cutO H hα hspan hSupport i z

/-- The complete symbolic Q output agrees with O's dependent
rooted word at ALL ambient bounded positions, not only at
selected projected roots. The proof uses actual original
ambient-fibre uniformity, which follows from the two-letter
span refinement of the NEW genuine enlarged final word. -/
theorem coherent_target_Q_matches_full_word
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
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (coherentTargetInput hb g f fallback O cutO H hSupport)
        s) = O.word.word s := by
  let w := coherentTargetInput hb g f fallback O cutO H hSupport
  let e := sourceOutputVarsEquiv hb g O cutO H
  have hOrig : O.word.span ⊆ g.ambient.span :=
    fun ψ hψ =>
      (enlargedInterpolatedFinalWord_span_subset
        g f fallback) (hspan hψ)
  cases hs : g.ambient.word s with
  | inl a =>
      have hQ :
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s = Sum.inl a :=
        ForwardQAmbientFibreSymbol.fibreQ_original_constant
          g fallback w s a hs
      have hO : O.word.word s = Sum.inl a :=
        SpanAudit.constant_preserved_of_span_subset
          hα g.ambient.word O.word.word hOrig hs
      simp [hQ,hO]
  | inr u =>
      have hQ :
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s =
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w u.1 :=
        ForwardQAmbientFibreSymbol.fibreQ_constant_on_ambient_fibre
          g fallback w u s u.1 hs (g.ambient.atRoot u)
      have hO : O.word.word s = O.word.word u.1 :=
        SpanAudit.fibre_uniform_of_span_subset
          hα g.ambient.word O.word.word hOrig hs (g.ambient.atRoot u)
      calc
        Sum.map id e
          (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w s) =
          Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w u.1) := congrArg (Sum.map id e) hQ
        _ = O.word.word u.1 :=
          coherent_target_Q_matches_at_original_f_root
            hb g f fallback O cutO H hα hspan hSupport u
        _ = O.word.word s := hO.symm

/-- Full RAW reverse preimage for the genuine enlarged local
Ramsey word: its mixed-product span contains an actual input
with precisely O's Q node SET and complete dependent word,
under canonical source/target variable-root transport.

The chosen target D₂ point tuple has not yet been certified
as a corrected starred-domain input here, and the printed
reverse-lex W_* domain is not identified with it. -/
theorem exists_raw_enlarged_target_Q_preimage
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
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedInput g.core,
      w ∈ f.span ∧
      nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback w) =
        O.tree.toFinset ∧
      ∀ s : BoundedNode b n,
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w s) =
          O.word.word s := by
  refine ⟨coherentTargetInput hb g f fallback O cutO H hSupport,
    coherentTargetInput_mem_mixed_span hb g f fallback O cutO H hSupport,
    ForwardQFinalGenericTargetNodeSet.coherent_enlarged_target_Q_node_set_eq
      hb g f fallback O cutO H hSupport,
    ?_⟩
  intro s
  exact coherent_target_Q_matches_full_word
    hb g f fallback O cutO H hα hspan hSupport s

end DualTree.ForwardQFinalEnlargedTargetWholeWord
