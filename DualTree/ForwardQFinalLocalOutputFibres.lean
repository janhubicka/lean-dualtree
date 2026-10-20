import DualTree.ForwardQFinalMixedAlphabetSpan
import DualTree.ForwardQFinalGlobalFibreSubstitution

/-!
# Output-symbol agreement on the genuine local mixed-word fibres

The target O need not be encoded by independently chosen letters at
each P_i(z): those pointwise witnesses could vary along the same
component-variable fibre and leave the local Ramsey span.

The actual final interpolated ambient word f' reads the true local
component symbol at P_i(z). It therefore gives the SAME syntactic
symbol on P_i(z) and P_i(v) whenever the local mixed component word
has symbol v at z. The two-letter span-substitution theorem forces
O's ACTUAL dependent word symbols to agree at those positions.
Original local constants also remain constant in O.

These facts provide the real uniformity needed to choose one enlarged
auxiliary letter per local component variable root. Full Q-object
reconstruction and the particular coherent input are separate.
-/

namespace DualTree.ForwardQFinalLocalOutputFibres

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalLocalSymbolTransport

/-- At every true P_i(z), the actual interpolated final ambient
variable word has precisely the locally decoded component symbol.
The equality is on the whole typed ambient-word function, not merely
the abstract global-root substitution. -/
theorem interpolatedFinalWord_at_projected
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    (interpolatedFinalWord g f (fun a : α => a) fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
      localSymbol g f (fun a : α => a) fallback i z := by
  let p := ForwardQActualCoordinateWord.projectLocal g.core i z
  have hroot :
      g.ambient.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g p.1 p.2) := by
    change g.ambient.word
        (ForwardQAmbientFibreFrame.ambientAtTRoot g p.1 p.2).1 =
      Sum.inr (ForwardQAmbientFibreFrame.ambientAtTRoot g p.1 p.2)
    exact ForwardQAmbientFibreFrame.ambient_at_T_root_symbol g p.1 p.2
  change SpanAudit.substitute g.ambient.word
    (globalRootSymbol g f (fun a : α => a) fallback)
    (ForwardQActualCoordinateWord.projectedBounded
      g.core g.T_bounded i z) =
      localSymbol g f (fun a : α => a) fallback i z
  calc
    _ = globalRootSymbol g f (fun a : α => a) fallback
        (ForwardQAmbientFibreFrame.ambientAtTRoot g p.1 p.2) := by
      simp [SpanAudit.substitute, hroot]
    _ = localSymbol g f (fun a : α => a) fallback i z :=
      globalRootSymbol_projected g f (fun a : α => a) fallback i z

/-- Every old local component variable is read uniformly at all its
occurrences, including at its literal local variable root. -/
theorem localSymbol_constant_on_component_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    localSymbol g f (fun a : α => a) fallback i z =
      localSymbol g f (fun a : α => a) fallback i v.1 := by
  have hroot := (f.vector.components i).toVariableWord.atRoot v
  simp [localSymbol, hz, hroot]

/-- Consequently, f' bears the same ACTUAL dependent symbol at
P_i(z) and P_i(v) whenever f_i(z) is the local variable v. -/
theorem interpolatedFinalWord_constant_on_local_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    (interpolatedFinalWord g f (fun a : α => a) fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    (interpolatedFinalWord g f (fun a : α => a) fallback).word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i v.1) := by
  calc
    _ = localSymbol g f (fun a : α => a) fallback i z :=
      interpolatedFinalWord_at_projected g f fallback i z
    _ = localSymbol g f (fun a : α => a) fallback i v.1 :=
      localSymbol_constant_on_component_variable_fibre
        g f fallback i v z hz
    _ = (interpolatedFinalWord g f (fun a : α => a) fallback).word
          (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i v.1) :=
      (interpolatedFinalWord_at_projected g f fallback i v.1).symm

/-- If O's evaluated span refines the real interpolated f' span
over two letters, O's own dependent word symbols are forced to
agree across every component-variable fibre. -/
theorem output_constant_on_local_variable_fibre
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan :
      O.word.span ⊆
        (interpolatedFinalWord g f (fun a : α => a) fallback).span)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (f.vector.components i).word z = Sum.inr v) :
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i v.1) := by
  obtain ⟨ρ, hword⟩ :=
    (VariableWord.span_subset_iff_substitution hα
      (interpolatedFinalWord g f (fun a : α => a) fallback)
      O.word).1 hspan
  have hfEq :=
    interpolatedFinalWord_constant_on_local_variable_fibre
      g f fallback i v z hz
  calc
    O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
        SpanAudit.substitute
          (interpolatedFinalWord g f (fun a : α => a) fallback).word
          ρ (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i z) :=
      congrFun hword _
    _ = SpanAudit.substitute
          (interpolatedFinalWord g f (fun a : α => a) fallback).word
          ρ (ForwardQActualCoordinateWord.projectedBounded
            g.core g.T_bounded i v.1) := by
      simp [SpanAudit.substitute, hfEq]
    _ = O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i v.1) :=
      (congrFun hword _).symm

/-- Original constant letters in the local mixed component word
stay actual original constants of the target O at P_i(z). -/
theorem output_preserves_local_component_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan :
      O.word.span ⊆
        (interpolatedFinalWord g f (fun a : α => a) fallback).span)
    (i : Index g.core)
    (z : BoundedNode b (k - (m + 1)))
    (a : α)
    (hz : (f.vector.components i).word z = Sum.inl a) :
    O.word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) = Sum.inl a := by
  have hLocal :
      localSymbol g f (fun x : α => x) fallback i z = Sum.inl a := by
    simpa using localSymbol_constant
      g f (fun x : α => x) fallback i z a hz
  have hfConstant :
      (interpolatedFinalWord g f (fun x : α => x) fallback).word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) = Sum.inl a :=
    (interpolatedFinalWord_at_projected g f fallback i z).trans hLocal
  exact SpanAudit.constant_preserved_of_span_subset
    hα (interpolatedFinalWord g f (fun x : α => x) fallback).word
    O.word.word hspan hfConstant

end DualTree.ForwardQFinalLocalOutputFibres
