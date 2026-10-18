import DualTree.ForwardQFinalInducedStarredPoint
import DualTree.ForwardQAmbientFibreLegalWord
import DualTree.ForwardQAmbientFibreSpan

/-!
# Genuine fibrewise Q output equals evaluated f' on safe original f-fibres

The previous corrected-Q comparison was formulated at the projected
ambient roots, using the ordinary-alphabet coordinate decoder.
Here we pass to the ACTUAL fibrewise starred Q construction that
reads the original ambient f-variable at EVERY position.

An ordinary mixed-product input x embeds into the enlarged alphabet
Sum alpha (Fin (m+1)) using only original-letter constructors.
For every assignment to the selected final roots, the already
checked canonical induced starred point lies in the mixed word span;
the enlarged embedding preserves its corrected D2 starred condition.

The true fibrewise Q-word is a legal starred word with old source
variable names. On the ENTIRE original ambient f-fibre rooted at
P_i(z), its actual word symbol is the original-alphabet constant
carrying the corresponding evaluated f' letter. Hence ANY evaluation
of the old source variables produces the same evaluated f' letter
on that whole fibre.

This is specific to safe projected f-fibres and original-letter
inputs. Auxiliary cone letters, early f-fibres, and unsafe fibres
require separate comparison. It does not assert whole-word equality,
Definition 24 simplicity, or the printed reverse-starred W_* theorem.
-/

namespace DualTree.ForwardQFinalWholeFibreQEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalFibreEvaluation
open ForwardQFinalInducedStarredPoint

/-- An ordinary mixed input regarded as an enlarged input with
no auxiliary letters. In particular all genuine D2 points are
preserved literally rather than reconstructed after erasure. -/
def liftOrdinary
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c) :
    ForwardQEnlargedConstantWords.EnlargedInput c where
  words := fun i z => Sum.inl (x.words i z)
  upPoint := x.upPoint
  bulletPoint := x.bulletPoint

/-- Erasing the auxiliary alphabet from an ordinary lifted
mixed input recovers the exact original mixed point. -/
theorem eraseAux_liftOrdinary
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (fallback : α)
    (x : Input c) :
    ForwardQEnlargedConstantWords.eraseAux c fallback
      (liftOrdinary c x) = x := by
  cases x
  rfl

/-- Lift an ACTUAL corrected starred input, keeping its
starred condition unchanged because D2 points are unchanged. -/
noncomputable def liftedStarred
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (fallback : α)
    (x : ForwardQActualStarredSpace.StarredInput c) :
    ForwardQEnlargedConstantWords.EnlargedStarredInput c fallback := by
  refine ⟨liftOrdinary c x.1, ?_⟩
  change ForwardQActualStarredSpace.IsStarred c
    (ForwardQEnlargedConstantWords.eraseAux c fallback
      (liftOrdinary c x.1))
  rw [eraseAux_liftOrdinary]
  exact x.2

/-- The ACTUAL finished fibrewise starred Q output on the
canonically induced mixed-product point, not a position-patched
symbol stand-in. -/
noncomputable def inducedFibreQ
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) :=
  ForwardQAmbientFibreLegalWord.fibreQStarredWord
    hb g fallback
    (liftedStarred g.core fallback
      (inducedStarredInput g f fallback σ hq))

/-- On EVERY position of the original ambient f-fibre rooted
at P_i(z), the ACTUAL fibrewise Q symbol is the constant
carrying the evaluation of the interpolated final word.
No assumption on which old source variables are evaluated is
needed at these late fibres. -/
theorem inducedFibreQ_symbol_on_safe_fibre
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (i : Index g.core)
    (z : BoundedNode b (k - (m+1)))
    (s : BoundedNode b n)
    (hs : g.ambient.word s =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2)) :
    (inducedFibreQ hb g f fallback σ hq).word.word s =
      Sum.inl (SpanAudit.evalSymbol σ
        ((interpolatedFinalWord g f (fun a : α => a) fallback).word s)) := by
  let x := inducedStarredInput g f fallback σ hq
  let w := liftedStarred g.core fallback x
  have hQ :
      (inducedFibreQ hb g f fallback σ hq).word.word s =
        Sum.inl (x.1.words i z) := by
    have hfull :=
      ForwardQAmbientFibreLegalWord.fibreQStarredWord_projected_full_fibre
        hb g fallback w i z s hs
    simpa only [inducedFibreQ, x, w, liftedStarred, liftOrdinary]
      using hfull
  have hcoord :
      x.1.words i z =
      SpanAudit.eval (f.vector.components i).word
        (localAssignment g f fallback σ i) z := rfl
  have heval :
      SpanAudit.evalSymbol σ
        ((interpolatedFinalWord g f (fun a : α => a) fallback).word s) =
      SpanAudit.eval (f.vector.components i).word
        (localAssignment g f fallback σ i) z := by
    let u := ForwardQAmbientFibreFrame.ambientAtTRoot g
      (projected g.core ⟨i,z⟩).1
      (projected g.core ⟨i,z⟩).2
    exact interpolatedFinalWord_fibre_eval
      g f fallback σ u s hs i z rfl
  calc
    (inducedFibreQ hb g f fallback σ hq).word.word s =
        Sum.inl (x.1.words i z) := hQ
    _ = Sum.inl (SpanAudit.eval (f.vector.components i).word
        (localAssignment g f fallback σ i) z) :=
          congrArg Sum.inl hcoord
    _ = Sum.inl (SpanAudit.evalSymbol σ
        ((interpolatedFinalWord g f (fun a : α => a) fallback).word s)) :=
          congrArg Sum.inl heval.symm

/-- Even after evaluating the OLD Q source variable names under
an arbitrary assignment tau, the true Q output and the
interpolated ambient final word have equal constant values at
every position of an original safe projected f-fibre. -/
theorem inducedFibreQ_eval_on_safe_fibre
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (τ : (inducedFibreQ hb g f fallback σ hq).word.Vars → α)
    (i : Index g.core)
    (z : BoundedNode b (k - (m+1)))
    (s : BoundedNode b n)
    (hs : g.ambient.word s =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2)) :
    ((inducedFibreQ hb g f fallback σ hq).word.eval τ) s =
    ((interpolatedFinalWord g f (fun a : α => a) fallback).eval σ) s := by
  change
    SpanAudit.evalSymbol τ
      ((inducedFibreQ hb g f fallback σ hq).word.word s) =
    SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f (fun a : α => a) fallback).word s)
  rw [inducedFibreQ_symbol_on_safe_fibre
    hb g f fallback σ hq i z s hs]
  rfl

/-- Independently, this ACTUAL starred fibrewise Q output
is an evaluated-span refinement of the original ambient f
on the ENTIRE homogeneous tree, not just on safe cones. -/
theorem inducedFibreQ_span_subset_ambient
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    (inducedFibreQ hb g f fallback σ hq).word.span ⊆
      g.ambient.span :=
  ForwardQAmbientFibreSpan.fibreQStarredWord_span_subset_ambient
    hb g fallback
    (liftedStarred g.core fallback
      (inducedStarredInput g f fallback σ hq))

end DualTree.ForwardQFinalWholeFibreQEvaluation
