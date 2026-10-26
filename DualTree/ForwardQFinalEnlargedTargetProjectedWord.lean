import DualTree.ForwardQFinalGenericTargetNodeSet
import DualTree.ForwardQFinalEnlargedTargetLocalFibres
import DualTree.ForwardQFinalOutputProjectedEncoder

/-!
# Genuine enlarged mixed-span Q word matches the target at P_i(z)

Let f be the actual Corollary-22 local variable word with its
ENLARGED alphabet α ⊕ Fin(m+1). Under the same-complete-signature,
two-letter and target span-inclusion premises, the coherent target
input chooses the genuine local D₂ support points and one enlarged
letter per actual component-variable fibre.

The Q symbol agrees with the TARGET dependent word at every safe
projected ambient f-root P_i(z). The proof has three genuine cases:

* original fixed α constants are preserved by the target;
* fixed auxiliary constants j are decoded by R_i into an old
  target variable (or an original constant), as forced by the
  new symbolic span-rigidity lemma; and
* actual local variables share one chosen enlarged letter, whose
  encoded Q symbol is equal at its root to the requested O symbol,
  which is itself constant on that local variable fibre.

This is exact dependent WORD-SYMBOL equality, not merely one
evaluated-word equality. The initial/unsafe fibres and final D₂
starred certificate remain separate requirements.
-/

namespace DualTree.ForwardQFinalEnlargedTargetProjectedWord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalOutputProjectedEncoder
open ForwardQFinalEnlargedTargetLocalFibres
open ForwardQFinalEnlargedTargetInput

/-- The actual Q output of the coherent GENUINE enlarged mixed
Ramsey span point matches the requested target's dependent
variable-word symbol at every safe projected T root, under the
canonical old/target-root equivalence.

Fixed auxiliary constants are decoded faithfully, rather than
silently replaced by arbitrary original-alphabet letters. -/
theorem coherent_target_Q_matches_at_projected
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
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback
        (coherentTargetInput hb g f fallback O cutO H hSupport)
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) := by
  let w := coherentTargetInput hb g f fallback O cutO H hSupport
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
      cases a with
      | inl a0 =>
          have hw : w.words i z = Sum.inl a0 := by
            simp [w, coherentTargetInput, hz]
          have hsymbol :
              ForwardQAmbientFibreSymbol.fibreQSymbol
                g fallback w p = Sum.inl a0 := by
            rw [hw] at hQ
            simpa using hQ
          have hO :
              O.word.word p = Sum.inl a0 :=
            output_preserves_original_local_constant
              g f fallback O hα hspan i z a0 hz
          change Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w p) = O.word.word p
          rw [hsymbol,hO]
          rfl
      | inr j =>
          have hw : w.words i z = Sum.inr j := by
            simp [w, coherentTargetInput, hz]
          have hsymbol :
              ForwardQAmbientFibreSymbol.fibreQSymbol
                g fallback w p =
              ForwardQVisibleAncestorDecoder.decodeAux
                g.core fallback i j := by
            rw [hw] at hQ
            simpa using hQ
          have hO :=
            output_preserves_aux_local_constant
              hb g f fallback O cutO H hα hspan i z j hz
          change Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w p) = O.word.word p
          rw [hsymbol]
          exact hO.symm
  | inr v =>
      have hw :
          w.words i z =
            encodeProjectedOutputSymbol
              hb g O cutO H fallback i v.1 := by
        simp [w, coherentTargetInput, hz]
      rw [hw] at hQ
      have hroot :=
        decoded_encoded_projected_output_symbol
          hb g O cutO H fallback i v.1
      have hO :=
        output_constant_on_local_variable_fibre
          g f fallback O hα hspan i v z hz
      calc
        Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w p) =
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

end DualTree.ForwardQFinalEnlargedTargetProjectedWord
