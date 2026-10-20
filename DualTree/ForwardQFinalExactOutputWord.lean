import DualTree.ForwardQFinalUnsafeConeReconstruction
import DualTree.ForwardQFinalSafeRootAgreement
import DualTree.ForwardQFinalUnsafeOutputConstant

/-!
# Exact source-facing Q/output word symbols in Lemma 27

The true fibrewise Q output and every same-complete-signature starred
output O refining the final interpolated f' have equal dependent
word symbols at ALL original ambient homogeneous positions, after
the canonical root-preserving equivalence of old/output variables,
provided the alphabet has at least two distinct letters.

Early roots: actual complete signature.
Safe late roots: exact R_i symbol encoding at true P_i(z).
Unsafe late roots: both Q and O are literal fallback constants.
Original f-fibre uniformity transports root equality everywhere.

This theorem is about EXACT WORD SYMBOLS, not the full starred
object, terminal D2 reconstruction or local mixed-product span.
-/

namespace DualTree.ForwardQFinalExactOutputWord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalOutputProjectedEncoder
open ForwardQFinalUnsafeConeReconstruction

/-- The actual fibrewise Q map uses its literal fallback at ANY
original ambient-f variable root after the corrected cut which has
no safe projected coordinate. The selected-frontier-some branch is
covered by genuine inverse short-tail reconstruction, not guessed. -/
theorem actual_Q_fallback_at_unsafe_late_root
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = none) :
    ForwardQAmbientFibreSymbol.fibreQSymbol
      g fallback w u.1 = Sum.inl fallback := by
  have hT : u.1.1 ∈ g.core.T :=
    (g.ambient_support_T u.1).1 u.2
  have hroot : g.ambient.word u.1 = Sum.inr u :=
    g.ambient.atRoot u
  rw [ForwardQAmbientFibreSymbol.fibreQ_after_cut
    g fallback w u.1 u hroot hafter]
  unfold ForwardQAmbientFibreSymbol.decodeAmbientRoot
  cases hi : ForwardQFullFrontierWord.selectedFrontier
      g.core u.1 with
  | none =>
      simp [hi]
  | some i =>
      have hfront : IsPrefix
          (ForwardOrderedProjections.frontierAt
            g.core.T g.core.cut i).1 u.1.1 :=
        ForwardQAmbientFibreSymbol.selectedFrontier_some_prefix
          g.core u.1 i hi
      have hsample :
          ForwardQEnlargedConstantWords.sampledEnlarged
            g.core w fallback i u.1 = Sum.inl fallback :=
        sampledEnlarged_fallback_of_no_safe
          g.core fallback w i u.1 hT hfront hnone
      simp [hi, hsample]

/-- The verified two-letter output-span containment supplies the
same fallback constant on every unsafe late ambient-f root. Hence
that root's actual Q symbol matches O after the real dependent-root
transport. -/
theorem actual_Q_matches_output_on_unsafe_late_root
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
    (hspan :
      O.word.span ⊆
        (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
          g f (fun x : α => x) fallback).span)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hnone : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = none) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1) = O.word.word u.1 := by
  have hQ : ForwardQAmbientFibreSymbol.fibreQSymbol
      g fallback w u.1 = Sum.inl fallback :=
    actual_Q_fallback_at_unsafe_late_root g fallback w u hafter hnone
  have hO : O.word.word u.1 = Sum.inl fallback :=
    ForwardQFinalUnsafeOutputConstant.unsafe_late_output_word_constant
      g f fallback O hα hspan u hafter hnone
  simp [hQ, hO]

/-- Under the concrete hypotheses of the corrected Lemma 27 forward
construction, the genuine relettered Q matches the actual starred
output's entire dependent WORD FUNCTION at every original bounded
homogeneous position. No residual unsafe-root hypothesis remains. -/
theorem actual_relettered_Q_word_eq_output
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
    (hspan :
      O.word.span ⊆
        (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
          g f (fun x : α => x) fallback).span)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (reletterInputFromOutput hb g O cutO H fallback base)
        s) = O.word.word s := by
  have hunsafe :
      ∀ u : g.ambient.Vars,
        ¬ ForwardAux u.1.1 g.core.cut →
        ForwardQFinalSafeAddressLookup.safeAddress
          g.core u.1.1 = none →
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback
              (reletterInputFromOutput hb g O cutO H fallback base)
            u.1) = O.word.word u.1 := by
    intro u hafter hnone
    exact actual_Q_matches_output_on_unsafe_late_root
      hb g f fallback O cutO H hα hspan
      (reletterInputFromOutput hb g O cutO H fallback base)
      u hafter hnone
  exact ForwardQFinalSafeRootAgreement.reletter_Q_word_eq_of_unsafe_late_root_agreement
    hb g f fallback O cutO H hα hspan base hunsafe s

end DualTree.ForwardQFinalExactOutputWord
