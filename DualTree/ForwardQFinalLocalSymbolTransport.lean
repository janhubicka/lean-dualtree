import DualTree.ForwardQFinalSelectedVariableTransport

/-!
# Decode a genuine local Ramsey-variable symbol into a final f' root

The corrected final support is already (m+q)-complete skew. Its
selected local variables have been embedded injectively into a
single bounded global-root type, preserving each actual frontier
tag (not reusing the much smaller old starred source root type).

Here a local component symbol is converted into the alphabet
of the eventual ambient f': constants use a supplied decoding
beta -> alpha, and a variable v is transported to P_i(v) IF
its rank-budgeted global root was retained. Variables discarded
by the m+1 frontier's one-level-shorter budget are explicitly
constantized to a supplied fallback letter, rather than
silently asserting their roots were selected.

The resulting map has exact root emission at every SELECTED
local variable, and every emitted global variable root is
a prefix of the actual projected ambient position P_i(z).
These are the two principal fibrewise proof obligations needed
to build a root-compatible global substitution on the original
ambient f roots. The total root selection and whole-domain
interpolation are not claimed here.
-/

namespace DualTree.ForwardQFinalLocalSymbolTransport

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport

/-- A decoded local variable-word symbol in ONE corrected sorted
frontier, with symbols rooted at precisely the selected final
global ambient roots. This does NOT identify independent
variables from distinct frontier indices. -/
noncomputable def localSymbol
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    Sum α {t : BoundedNode b n // t ∈ boundedFinalRoots g f} := by
  classical
  exact match (f.vector.components i).word z with
    | Sum.inl a => Sum.inl (decode a)
    | Sum.inr v =>
        if hv : (⟨i,v.1⟩ : LocalAddress g.core) ∈
            selectedLocalRoots g.core f (m+q) then
          Sum.inr (selectedBoundedRoot g f ⟨⟨i,v.1⟩,hv⟩)
        else
          Sum.inl fallback

/-- Genuine local constants decode directly to ambient alphabet
letters; they are not turned into spurious variable names. -/
theorem localSymbol_constant
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) (a : β)
    (hword : (f.vector.components i).word z = Sum.inl a) :
    localSymbol g f decode fallback i z = Sum.inl (decode a) := by
  simp [localSymbol, hword]

/-- A local variable omitted by the exact M=m+q rank filter
is deliberately made constant. This includes the excluded
highest local level in the rank-(m+1) frontier band. -/
theorem localSymbol_excluded_variable
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (v : (f.vector.components i).Vars)
    (hword : (f.vector.components i).word z = Sum.inr v)
    (hnot :
      (⟨i,v.1⟩ : LocalAddress g.core) ∉
        selectedLocalRoots g.core f (m+q)) :
    localSymbol g f decode fallback i z = Sum.inl fallback := by
  simp [localSymbol, hword, hnot]

/-- At its OWN local variable root v, an actually selected
variable is emitted as the precisely tagged final global root
P_i(v), using the original local word's atRoot axiom. -/
theorem localSymbol_at_selected_root
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (hselected :
      (⟨i,v.1⟩ : LocalAddress g.core) ∈
        selectedLocalRoots g.core f (m+q)) :
    localSymbol g f decode fallback i v.1 =
      Sum.inr
        (selectedBoundedRoot g f ⟨⟨i,v.1⟩,hselected⟩) := by
  have hroot :
      (f.vector.components i).word v.1 = Sum.inr v :=
    (f.vector.components i).toVariableWord.atRoot v
  simp [localSymbol, hroot, hselected]

/-- Every variable symbol emitted by the decoded local word
is rooted at an actual selected final ambient root BELOW
its projected original-T position P_i(z). This is the
genuine syntactic root-compatibility condition, not an
inferred span property or a Hall capacity assumption. -/
theorem localSymbol_variable_below
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (v : {t : BoundedNode b n // t ∈ boundedFinalRoots g f})
    (hletter : localSymbol g f decode fallback i z = Sum.inr v) :
    IsPrefix v.1.1 (projected g.core ⟨i,z⟩).1 := by
  cases hw : (f.vector.components i).word z with
  | inl a =>
      simp [localSymbol, hw] at hletter
  | inr u =>
      by_cases hselected :
          (⟨i,u.1⟩ : LocalAddress g.core) ∈
            selectedLocalRoots g.core f (m+q)
      · have himage :
            selectedBoundedRoot g f ⟨⟨i,u.1⟩,hselected⟩ = v := by
          have hs :
              (Sum.inr
                (selectedBoundedRoot g f ⟨⟨i,u.1⟩,hselected⟩) :
                Sum α {t : BoundedNode b n //
                  t ∈ boundedFinalRoots g f}) = Sum.inr v := by
            simpa [localSymbol, hw, hselected] using hletter
          exact Sum.inr.inj hs
        rw [← himage]
        exact selected_local_variable_prefix_projected
          g f i u z hw hselected
      · simp [localSymbol, hw, hselected] at hletter

end DualTree.ForwardQFinalLocalSymbolTransport
