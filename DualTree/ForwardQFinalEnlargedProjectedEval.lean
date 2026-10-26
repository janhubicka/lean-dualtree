import DualTree.ForwardQFinalEnlargedInducedEvaluation

/-!
# Actual corrected Q agrees with the genuine enlarged final word at P_i(z)

The source-facing Corollary-22 handoff requires a local Ramsey
variable word over the ENLARGED alphabet, whose fixed auxiliary
letters may be decoded to OLD source variable roots. The genuine
global final word and an actual starred mixed input are already
constructed independently, with all local fixed symbols preserved.

For any final assignment σ and an old-source assignment τ agreeing
on the retained old roots, we now compare their evaluations at
every actual safe projected T root P_i(z). The only new case
relative to the old original-alphabet proof is a FIXED auxiliary
local constant j: its Q-image reads R_i(j) as an old source variable
(or original constant), while the final interpolation reads the
same R_i(j) embedded as a retained final root. Old-root assignment
compatibility proves exact equality in this case.

The proof compares actual fibrewise Q symbols, not a surrogate
position-based decoder, and it never assumes a map from all
enlarged constants to the original alphabet.

This is the projected-root agreement component of the enlarged
forward-evaluation bridge. The other original ambient f-fibres,
and the reverse starred target preimage, remain separate.
-/

namespace DualTree.ForwardQFinalEnlargedProjectedEval

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedLocalSymbols
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQFinalHeightBudget

/-- At every actual safely projected ambient T root, the genuine
FINAL variable word (whose local constants are truly enlarged)
emits precisely the decoded local symbol, including all auxiliary
constants interpreted as retained OLD roots. -/
theorem enlargedFinalWord_projected_root_symbol
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    (enlargedInterpolatedFinalWord g f fallback).word
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2).1 =
      enlargedLocalSymbol g f fallback i z := by
  let u := ForwardQAmbientFibreFrame.ambientAtTRoot g
    (projected g.core ⟨i,z⟩).1
    (projected g.core ⟨i,z⟩).2
  have hroot : g.ambient.word u.1 = Sum.inr u :=
    g.ambient.atRoot u
  change SpanAudit.substitute g.ambient.word
    (enlargedGlobalRootSymbol g f fallback) u.1 =
      enlargedLocalSymbol g f fallback i z
  calc
    SpanAudit.substitute g.ambient.word
        (enlargedGlobalRootSymbol g f fallback) u.1 =
        enlargedGlobalRootSymbol g f fallback u := by
          simp [SpanAudit.substitute, hroot]
    _ = enlargedLocalSymbol g f fallback i z :=
      enlargedGlobalRootSymbol_projected g f fallback i z

/-- At EVERY SAFE projected original f-variable root P_i(z),
evaluation of the actual CORRECTED fibrewise Q output agrees
with evaluation of the actual newly constructed enlarged final
word, under the explicit old-source-root assignment relation.

All local constant cases—including auxiliary j decoded to a
retained variable—and selected/nonselected local variable
cases are handled by genuine algebraic evaluation. The
starred input used is precisely the verified member of f.span. -/
theorem enlarged_Q_projected_eval_eq_final
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (hcompat : OldRootAssignmentCompatible g f σ τ)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ)
        (ForwardQAmbientFibreFrame.ambientAtTRoot g
          (projected g.core ⟨i,z⟩).1
          (projected g.core ⟨i,z⟩).2).1) =
    SpanAudit.evalSymbol σ
      ((enlargedInterpolatedFinalWord g f fallback).word
        (ForwardQAmbientFibreFrame.ambientAtTRoot g
          (projected g.core ⟨i,z⟩).1
          (projected g.core ⟨i,z⟩).2).1) := by
  have hQ :=
    ForwardQAmbientFibreSymbol.fibreQ_projected_root
      g fallback (enlargedInducedInput g f fallback σ) i z
  have hnode :
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (ForwardQActualCoordinateWord.projectLocal g.core i z).1
        (ForwardQActualCoordinateWord.projectLocal g.core i z).2).1 =
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2).1 := rfl
  rw [hnode] at hQ
  have hW :=
    enlargedInducedInput_word_at g f fallback σ i z
  have hF := enlargedFinalWord_projected_root_symbol
    g f fallback i z
  rw [hQ, hW, hF]
  cases hw : (f.vector.components i).word z with
  | inl letter =>
      cases letter with
      | inl a =>
          simp [SpanAudit.evalSymbol, enlargedLocalSymbol, hw]
      | inr j =>
          simpa [SpanAudit.evalSymbol, enlargedLocalSymbol, hw] using
            (decodeAuxIntoFinal_eval_eq_source
              g f fallback σ τ hcompat i j).symm
  | inr v =>
      by_cases hselected :
          (⟨i,v.1⟩ : LocalAddress g.core) ∈
            selectedLocalRoots g.core f (m+q)
      · simp [SpanAudit.evalSymbol, chosenLocalLetter,
          enlargedLocalSymbol, hw, hselected]
      · simp [SpanAudit.evalSymbol, chosenLocalLetter,
          enlargedLocalSymbol, hw, hselected]

/-- The genuine enlarged final-word local symbol transports
uniformly through an entire ORIGINAL ambient variable fibre
rooted at P_i(z), not only through its root occurrence. -/
theorem enlargedFinalWord_projected_fibre_symbol
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (hu : u.1.1 = (projected g.core ⟨i,z⟩).1) :
    (enlargedInterpolatedFinalWord g f fallback).word s =
      enlargedLocalSymbol g f fallback i z := by
  have hsafe : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = some (⟨i,z⟩ : LocalAddress g.core) := by
    rw [hu]
    exact ForwardQFinalSafeAddressLookup.safeAddress_projected
      g.core ⟨i,z⟩
  change SpanAudit.substitute g.ambient.word
    (enlargedGlobalRootSymbol g f fallback) s =
    enlargedLocalSymbol g f fallback i z
  simp [SpanAudit.substitute, hs, enlargedGlobalRootSymbol, hsafe]


/-- The same genuine Q/f' evaluation equality holds on EVERY
occurrence of an original ambient f-variable whose root is a
safe projected point P_i(z), not merely at that root.

Both sides are constant on the whole original f-fibre: the Q
decoder is fibrewise on the original f root, while the final
word is a syntactic substitution of f with the exactly
decoded enlarged local symbol. -/
theorem enlarged_Q_projected_fibre_eval_eq_final
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (τ : g.core.source.word.Vars → α)
    (hcompat : OldRootAssignmentCompatible g f σ τ)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (s : BoundedNode b n)
    (hs : g.ambient.word s =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2)) :
    SpanAudit.evalSymbol τ
      (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ) s) =
    SpanAudit.evalSymbol σ
      ((enlargedInterpolatedFinalWord g f fallback).word s) := by
  let u := ForwardQAmbientFibreFrame.ambientAtTRoot g
    (projected g.core ⟨i,z⟩).1
    (projected g.core ⟨i,z⟩).2
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ) s =
      ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
        (enlargedInducedInput g f fallback σ) u.1 :=
    ForwardQAmbientFibreSymbol.fibreQ_constant_on_ambient_fibre
      g fallback (enlargedInducedInput g f fallback σ)
      u s u.1 hs (g.ambient.atRoot u)
  have hFibre :
      (enlargedInterpolatedFinalWord g f fallback).word s =
        enlargedLocalSymbol g f fallback i z :=
    enlargedFinalWord_projected_fibre_symbol
      g f fallback u s hs i z rfl
  have hRoot :
      (enlargedInterpolatedFinalWord g f fallback).word u.1 =
        enlargedLocalSymbol g f fallback i z := by
    change
      (enlargedInterpolatedFinalWord g f fallback).word
        (ForwardQAmbientFibreFrame.ambientAtTRoot g
          (projected g.core ⟨i,z⟩).1
          (projected g.core ⟨i,z⟩).2).1 =
        enlargedLocalSymbol g f fallback i z
    exact enlargedFinalWord_projected_root_symbol g f fallback i z
  have hFinal :
      (enlargedInterpolatedFinalWord g f fallback).word s =
      (enlargedInterpolatedFinalWord g f fallback).word u.1 :=
    hFibre.trans hRoot.symm
  calc
    SpanAudit.evalSymbol τ
        (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
          (enlargedInducedInput g f fallback σ) s) =
      SpanAudit.evalSymbol τ
        (ForwardQAmbientFibreSymbol.fibreQSymbol g fallback
          (enlargedInducedInput g f fallback σ) u.1) :=
      congrArg (SpanAudit.evalSymbol τ) hQ
    _ = SpanAudit.evalSymbol σ
        ((enlargedInterpolatedFinalWord g f fallback).word u.1) :=
      enlarged_Q_projected_eval_eq_final
        g f fallback σ τ hcompat i z
    _ = SpanAudit.evalSymbol σ
        ((enlargedInterpolatedFinalWord g f fallback).word s) :=
      congrArg (SpanAudit.evalSymbol σ) hFinal.symm

end DualTree.ForwardQFinalEnlargedProjectedEval
