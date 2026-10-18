import DualTree.ForwardQFinalGlobalFibreSubstitution
import DualTree.ForwardQActualCoordinateWord

/-!
# Evaluated fibrewise interpolation of the genuine ambient refinement

The corrected Lemma 27 final complete-skew support and a genuine
syntactic ambient refinement with that support are now constructed.
This module verifies the defining local-coordinate identity on
ENTIRE fibres of the original ambient f-variable word, not merely
on projected root positions.

A selected local variable v is evaluated at the globally distinct
root P_i(v); an omitted local variable is fixed to fallback.
Constants stay constants. Therefore every global assignment to
the final ambient variable roots canonically determines a
coordinate assignment to EACH mixed component, and evaluating
the refined ambient word over an original f-fibre rooted at
P_i(z) reproduces that component's evaluated word at z.

This is the local interpolation side of the corrected Q-span
comparison. The remaining step is to apply the actual Q of the
resulting mixed product point, establish membership in the
CORRECTED starred W_* domain, and transport Definition 24
simplicity/Ramsey colourings. No printed reverse-lex lemma is
claimed here.
-/

namespace DualTree.ForwardQFinalFibreEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalLocalSymbolTransport
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalSafeAddressLookup

/-- Given a global final-variable assignment, the local variable
v receives the value of its selected projected root P_i(v),
or the fixed fallback when the exact target rank filter
removes v. -/
noncomputable def localAssignment
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core) :
    (f.vector.components i).Vars → α := by
  classical
  exact fun v =>
    if h : (⟨i,v.1⟩ : LocalAddress g.core) ∈
        selectedLocalRoots g.core f (m+q) then
      σ (selectedBoundedRoot g f ⟨⟨i,v.1⟩,h⟩)
    else fallback

/-- Evaluating the genuine local-symbol decoder under a
GLOBAL assignment equals evaluating the original local
K-variable component with its induced assignment. -/
theorem localSymbol_eval
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    SpanAudit.evalSymbol σ
      (localSymbol g f (fun a : α => a) fallback i z) =
      SpanAudit.eval (f.vector.components i).word
        (localAssignment g f fallback σ i) z := by
  classical
  cases hw : (f.vector.components i).word z with
  | inl a =>
      simp [localSymbol, localAssignment,
        SpanAudit.eval, SpanAudit.evalSymbol, hw]
  | inr v =>
      by_cases hsel :
          (⟨i,v.1⟩ : LocalAddress g.core) ∈
            selectedLocalRoots g.core f (m+q)
      · simp [localSymbol, localAssignment,
          SpanAudit.eval, SpanAudit.evalSymbol, hw, hsel]
      · simp [localSymbol, localAssignment,
          SpanAudit.eval, SpanAudit.evalSymbol, hw, hsel]

/-- On ANY position in an original ambient f-variable fibre
rooted at the genuine projection P_i(z), the interpolated
global word emits exactly the local component's converted
symbol at z. This is not restricted to the variable root. -/
theorem interpolatedFinalWord_fibre_symbol
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (hu : u.1.1 = (projected g.core ⟨i,z⟩).1) :
    (interpolatedFinalWord g f decode fallback).word s =
      localSymbol g f decode fallback i z := by
  have hsafe : safeAddress g.core u.1.1 = some (⟨i,z⟩ : LocalAddress g.core) := by
    rw [hu]
    exact safeAddress_projected g.core ⟨i,z⟩
  change SpanAudit.substitute g.ambient.word
    (globalRootSymbol g f decode fallback) s =
      localSymbol g f decode fallback i z
  simp [SpanAudit.substitute, hs, globalRootSymbol, hsafe]

/-- In particular at every ACTUAL complete-T projected root,
the interpolated ambient word reads the local f_i symbol.
The genuine original f-root witness is used, not a new name. -/
theorem interpolatedFinalWord_projected_root_symbol
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    (interpolatedFinalWord g f decode fallback).word
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2).1 =
      localSymbol g f decode fallback i z := by
  let u := ForwardQAmbientFibreFrame.ambientAtTRoot g
    (projected g.core ⟨i,z⟩).1
    (projected g.core ⟨i,z⟩).2
  have hu : u.1.1 = (projected g.core ⟨i,z⟩).1 := rfl
  exact interpolatedFinalWord_fibre_symbol
    g f decode fallback u u.1
    (g.ambient.atRoot u) i z hu

/-- Evaluate the global final word at ANY original f-fibre
position rooted at P_i(z): the result is the actual local
component evaluation with independent selected-variable
values and explicitly constantized omitted variables. -/
theorem interpolatedFinalWord_fibre_eval
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (u : g.ambient.Vars)
    (s : BoundedNode b n)
    (hs : g.ambient.word s = Sum.inr u)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (hu : u.1.1 = (projected g.core ⟨i,z⟩).1) :
    SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f (fun a : α => a) fallback).word s) =
      SpanAudit.eval (f.vector.components i).word
        (localAssignment g f fallback σ i) z := by
  rw [interpolatedFinalWord_fibre_symbol
    g f (fun a : α => a) fallback u s hs i z hu]
  exact localSymbol_eval g f fallback σ i z

end DualTree.ForwardQFinalFibreEvaluation
