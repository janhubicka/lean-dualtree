import DualTree.ForwardQFinalSameTreeGamma2

/-!
# Γ₁ letters: extensionality of the actual enlarged Q encoder

The corrected Q decoder has a *surjective*, not necessarily injective,
map from the finite auxiliary alphabet onto visible old source roots.
Therefore equality of decoded symbols alone does not imply equality of
arbitrary enlarged letters.

However, the existing target encoder uses Classical.choose over the
FULL fibre of the fixed decoder. A choice from equal predicates is the
same choice, by propositional extensionality and proof irrelevance.
We establish that its defining predicate depends only on the
representation-independent rooted output symbol, not on the target's
dependent variable subtype or its complete-signature certificate.

In particular, equal rooted target symbols at the SAME actual projected
position imply equality of their concrete chosen enlarged Γ₁ letters.
No injectivity of the finite auxiliary decoder is assumed.
-/

namespace DualTree.ForwardQFinalEncoderExtensional

open ForwardSourceQTree
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalOutputProjectedEncoder

/-- Erase a symbol's variable-subtype witness to its actual bounded root. -/
def rootedSymbol
    {b n : Nat} {α β : Type*}
    (root : β → BoundedNode b n) :
    Sum α β → Sum α (BoundedNode b n)
  | Sum.inl a => Sum.inl a
  | Sum.inr v => Sum.inr (root v)

/-- The erasure of a dependent variable symbol is injective when
the variable's root uniquely determines that variable. -/
theorem rootedSymbol_injective
    {b n : Nat} {α β : Type*}
    (root : β → BoundedNode b n)
    (hroot : Function.Injective root) :
    Function.Injective (rootedSymbol (α := α) root) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl c =>
      exact congrArg Sum.inl (Sum.inl.inj h)
    | inr w =>
      cases h
  | inr v =>
    cases y with
    | inl c =>
      cases h
    | inr w =>
      exact congrArg Sum.inr (hroot (Sum.inr.inj h))

/-- The complete-signature variable equivalence preserves the
representation-independent rooted symbol, for EVERY source symbol. -/
theorem rootedSymbol_sourceOutputVarsEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (s : Sum α g.core.source.word.Vars) :
    rootedSymbol (fun v : O.word.Vars => v.1)
      (Sum.map id (sourceOutputVarsEquiv hb g O cutO H) s) =
    rootedSymbol (fun v : g.core.source.word.Vars => v.1) s := by
  cases s with
  | inl a => rfl
  | inr v =>
    change Sum.inr ((sourceOutputVarsEquiv hb g O cutO H v).1) =
      Sum.inr v.1
    rw [sourceOutputVarsEquiv_root]

/-- Choice from equivalent predicates is identical, even if their
existence witnesses were proved by unrelated arguments. This uses
proof irrelevance, NOT injectivity of the decoder. -/
theorem choose_eq_of_iff
    {β : Type*}
    (p q : β → Prop)
    (hp : ∃ a, p a) (hq : ∃ a, q a)
    (h : ∀ a, p a ↔ q a) :
    Classical.choose hp = Classical.choose hq := by
  have heq : p = q := funext fun a => propext (h a)
  cases heq
  rfl

/-- The target-dependent encoded-letter predicate can be rewritten
entirely in terms of the erased old-source root and the target's
root-labelled output. Consequently the predicates for two targets
are equivalent when their rooted symbols agree at this projected
position, even when their dependent variable types differ. -/
theorem projected_encoded_predicate_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g P cutP)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1)))
    (hobs :
      ForwardQSimpleLetterSmooth.rootLabel O
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z))
    (a : Sum α (Fin (m + 1))) :
    (Sum.map id (sourceOutputVarsEquiv hb g O cutO HO)
      (match a with
       | Sum.inl x => (Sum.inl x : Sum α g.core.source.word.Vars)
       | Sum.inr j =>
           ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) ↔
    (Sum.map id (sourceOutputVarsEquiv hb g P cutP HP)
      (match a with
       | Sum.inl x => (Sum.inl x : Sum α g.core.source.word.Vars)
       | Sum.inr j =>
           ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j) =
      P.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) := by
  let d : Sum α g.core.source.word.Vars :=
    match a with
    | Sum.inl x => Sum.inl x
    | Sum.inr j =>
        ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j
  let p := ForwardQActualCoordinateWord.projectedBounded
    g.core g.T_bounded i z
  have hO := rootedSymbol_sourceOutputVarsEquiv hb g O cutO HO d
  have hP := rootedSymbol_sourceOutputVarsEquiv hb g P cutP HP d
  have hinjO : Function.Injective
      (rootedSymbol (α := α) (fun v : O.word.Vars => v.1)) :=
    rootedSymbol_injective _ (fun x y h => Subtype.ext h)
  have hinjP : Function.Injective
      (rootedSymbol (α := α) (fun v : P.word.Vars => v.1)) :=
    rootedSymbol_injective _ (fun x y h => Subtype.ext h)
  constructor
  · intro h
    apply hinjP
    change rootedSymbol (fun v : P.word.Vars => v.1)
        (Sum.map id (sourceOutputVarsEquiv hb g P cutP HP) d) =
      ForwardQSimpleLetterSmooth.rootLabel P p
    calc
      _ = rootedSymbol (fun v : g.core.source.word.Vars => v.1) d := hP
      _ = rootedSymbol (fun v : O.word.Vars => v.1)
          (Sum.map id (sourceOutputVarsEquiv hb g O cutO HO) d) := hO.symm
      _ = ForwardQSimpleLetterSmooth.rootLabel O p :=
        congrArg (rootedSymbol (fun v : O.word.Vars => v.1)) h
      _ = ForwardQSimpleLetterSmooth.rootLabel P p := hobs
  · intro h
    apply hinjO
    change rootedSymbol (fun v : O.word.Vars => v.1)
        (Sum.map id (sourceOutputVarsEquiv hb g O cutO HO) d) =
      ForwardQSimpleLetterSmooth.rootLabel O p
    calc
      _ = rootedSymbol (fun v : g.core.source.word.Vars => v.1) d := hO
      _ = rootedSymbol (fun v : P.word.Vars => v.1)
          (Sum.map id (sourceOutputVarsEquiv hb g P cutP HP) d) := hP.symm
      _ = ForwardQSimpleLetterSmooth.rootLabel P p :=
        congrArg (rootedSymbol (fun v : P.word.Vars => v.1)) h
      _ = ForwardQSimpleLetterSmooth.rootLabel O p := hobs.symm

/-- Extensionality of the ACTUAL existing encoder, not a proposed
replacement: equal representation-independent rooted target
symbols at the same projected coordinate force the identical
chosen enlarged auxiliary letter. No artificial uniqueness
or injectivity of the raw auxiliary decoder is required. -/
theorem encodeProjectedOutputSymbol_eq_of_rootLabel
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O P : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO cutP : Node b)
    (HO : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (HP : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g P cutP)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1)))
    (hobs :
      ForwardQSimpleLetterSmooth.rootLabel O
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) =
      ForwardQSimpleLetterSmooth.rootLabel P
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) :
    encodeProjectedOutputSymbol hb g O cutO HO fallback i z =
      encodeProjectedOutputSymbol hb g P cutP HP fallback i z := by
  unfold encodeProjectedOutputSymbol
  apply choose_eq_of_iff
  intro a
  exact projected_encoded_predicate_iff
    hb g O P cutO cutP HO HP fallback i z hobs a

end DualTree.ForwardQFinalEncoderExtensional
