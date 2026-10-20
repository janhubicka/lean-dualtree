import DualTree.ForwardQFinalOutputProjectedEncoder
import DualTree.ForwardQFinalExactWordReduction
import DualTree.ForwardQFinalSafeAddressLookup

/-!
# Reduce exact Q-to-output word matching to unsafe post-cut roots

The actual Q formula is fibrewise on the original ambient f roots.
For a same-complete-signature starred output, the previous finite
decoder verifies Q/O symbol equality at every genuine P_i(z).

A root with a certified *safeAddress* is exactly a projected P_i(z).
This file transports that earlier equality along this actual address
identity. Combined with the two-letter fibre-uniformity theorem and
complete-signature agreement on old roots, it suffices to match Q/O
only on original ambient f roots AFTER the cut which have NO safe
projected address.

This does not prove the remaining unsafe-root equality and makes no
claim about full starred-object equality, D2 terminal reconstruction
or membership in the mixed-product Ramsey span.
-/

namespace DualTree.ForwardQFinalSafeRootAgreement

open ForwardSourceQTree
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalOutputProjectedEncoder

/-- No approximation is involved: each genuine safe ambient-f root is
one P_i(z), so the relettered Q symbol matches O at that exact root. -/
theorem reletter_Q_matches_output_at_safe_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (u : g.ambient.Vars)
    (a : ForwardQFinalRefinementRoots.LocalAddress g.core)
    (ha : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = some a) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (reletterInputFromOutput hb g O cutO H fallback base)
        u.1) = O.word.word u.1 := by
  rcases a with ⟨i,z⟩
  have hnode :
      u.1 = ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z := by
    apply Subtype.ext
    change u.1.1 =
      (ForwardQFinalRefinementRoots.projected g.core ⟨i,z⟩).1
    exact (ForwardQFinalSafeAddressLookup.safeAddress_spec
      g.core u.1.1 ⟨i,z⟩ ha).symm
  rw [hnode]
  exact reletterInput_Q_matches_output_at_projected
    hb g O cutO H fallback base i z

/-- The entire dependent word-symbol equality has now been reduced
to ambient-f variable roots strictly after the corrected cut AND
outside the finite safe P_i(z) projection image. Early roots come
from the true complete signature; safe late roots come from exact
local auxiliary decoding; the two-letter evaluated-span inclusion
then transfers equality across each original ambient-f fibre. -/
theorem reletter_Q_word_eq_of_unsafe_late_root_agreement
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
    (hunsafe :
      ∀ u : g.ambient.Vars,
        ¬ ForwardAux u.1.1 g.core.cut →
        ForwardQFinalSafeAddressLookup.safeAddress
          g.core u.1.1 = none →
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback
              (reletterInputFromOutput hb g O cutO H fallback base)
            u.1) = O.word.word u.1)
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (reletterInputFromOutput hb g O cutO H fallback base)
        s) = O.word.word s := by
  have hlate :
      ∀ u : g.ambient.Vars,
        ¬ ForwardAux u.1.1 g.core.cut →
        Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback
              (reletterInputFromOutput hb g O cutO H fallback base)
            u.1) = O.word.word u.1 := by
    intro u hcut
    cases hs : ForwardQFinalSafeAddressLookup.safeAddress
        g.core u.1.1 with
    | none => exact hunsafe u hcut hs
    | some a =>
        exact reletter_Q_matches_output_at_safe_root
          hb g O cutO H fallback base u a hs
  exact ForwardQFinalExactWordReduction.actual_Q_word_eq_of_late_root_agreement
    hb g f fallback O cutO H hα hspan
    (reletterInputFromOutput hb g O cutO H fallback base)
    hlate s

end DualTree.ForwardQFinalSafeRootAgreement
