import DualTree.ConeWordLift

/-!
# Root alignment of the three-way cone-word decoder

The Lemma 27 cone decoder distinguishes three symbol constructors:
* original alphabet letters, which remain constants;
* auxiliary letters, decoded to constants or visible source variables;
* genuine local cone variables, transported to chosen global variables.

For an actual output variable word, any occurrence of a target
variable at an ambient position t must have its chosen variable
root as an ambient prefix of t.

The generic lemma below proves this for the three-way decoder
from exactly two independent local obligations:
(A) when an auxiliary letter decodes to variable v at t,
    its target root prefixes t;
(B) when a genuine local variable z occurs at t,
    its chosen transported target root prefixes t.
Original constants impose no variable-root condition.

This is an exhaustive analysis of the typed constructors, not a
claim that the specific mixed cone words of Lemma 27 already meet
(A) and (B). Those obligations must be verified from the actual
source restriction and projection maps before assembling g_w.
-/

namespace DualTree.ThreeWayQDecoderRootAlignment

/-- The typed three-way decoding preserves the variable occurrence
prefix axiom provided auxiliary decoding and cone-variable root
transport each satisfy their own exact occurrence-prefix premise. -/
theorem liftWord_root_aligned
    {b n : Nat} {α Aux κ ν : Type*}
    (root : ν → Node b)
    (w : BoundedNode b n → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν)
    (variableRoot : κ → ν)
    (hAux : ∀ (t : BoundedNode b n) (a : Aux) (v : ν),
      w t = Sum.inl (Sum.inr a) →
      decodeAux a = Sum.inr v →
      IsPrefix (root v) t.1)
    (hCone : ∀ (t : BoundedNode b n) (z : κ),
      w t = Sum.inr z →
      IsPrefix (root (variableRoot z)) t.1)
    (t : BoundedNode b n)
    (v : ν)
    (h : ConeWordLift.liftWord w decodeAux variableRoot t =
      Sum.inr v) :
    IsPrefix (root v) t.1 := by
  cases hw : w t with
  | inl a =>
      cases a with
      | inl letter =>
          simp [ConeWordLift.liftWord, ConeWordLift.liftSymbol,
            hw] at h
      | inr auxiliary =>
          have hdecoded : decodeAux auxiliary = Sum.inr v := by
            simpa [ConeWordLift.liftWord, ConeWordLift.liftSymbol,
              hw] using h
          exact hAux t auxiliary v hw hdecoded
  | inr z =>
      have heq : variableRoot z = v := by
        simpa [ConeWordLift.liftWord, ConeWordLift.liftSymbol,
          hw] using h
      subst v
      exact hCone t z hw

/-- A family of local cone words, indexed by an arbitrary type,
is root-aligned pointwise once each index satisfies the same two
constructor-specific obligations. This is the interface needed
by a disjoint selected-D₂ cone patching operation. -/
theorem indexed_liftWord_root_aligned
    {b n : Nat} {α Aux κ ν ι : Type*}
    (root : ν → Node b)
    (w : ι → BoundedNode b n → Sum (Sum α Aux) κ)
    (decodeAux : ι → Aux → Sum α ν)
    (variableRoot : ι → κ → ν)
    (hAux : ∀ (i : ι) (t : BoundedNode b n)
      (a : Aux) (v : ν),
      w i t = Sum.inl (Sum.inr a) →
      decodeAux i a = Sum.inr v →
      IsPrefix (root v) t.1)
    (hCone : ∀ (i : ι) (t : BoundedNode b n) (z : κ),
      w i t = Sum.inr z →
      IsPrefix (root (variableRoot i z)) t.1)
    (i : ι) (t : BoundedNode b n) (v : ν)
    (h : ConeWordLift.liftWord
      (w i) (decodeAux i) (variableRoot i) t = Sum.inr v) :
    IsPrefix (root v) t.1 :=
  liftWord_root_aligned root (w i)
    (decodeAux i) (variableRoot i)
    (hAux i) (hCone i) t v h

end DualTree.ThreeWayQDecoderRootAlignment
