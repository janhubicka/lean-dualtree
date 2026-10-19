import DualTree.ForwardQFinalSignatureCompatibleCoverage
import DualTree.CutPreservation

/-!
# Fixed signature symbols imply the required early evaluated compatibility

Definition 26 of arXiv:2207.14599v1 fixes a PARTIAL SIGNATURE WORD
with rooted variable names. Its [S,f'] is a set of starred l-variable
refinements of f', not the full evaluated span of f'.

At an original f-variable root u at/before the corrected cut, the
fixed partial-signature condition is naturally an equality of
CutPreservation.underlyingSymbol, whose variable constructor carries
the actual bounded homogeneous root rather than an incompatible
dependent variable-name subtype.

If a further variable word h retains each OLD source root and its
underlying symbol at every early original f-root equals the fixed
source word g', then EVERY evaluation of h is early-compatible
with g' under a SINGLE assignment to the old source variables.
The proof simply reindexes h's variables at their genuine roots.

Combining this with the verified corrected Q fibrewise theorem gives
coverage of the evaluated span of any further refinement h of the
complete final f' satisfying this explicit signature condition.

This is the missing ALGEBRAIC bridge from a fixed rooted signature
to early evaluation compatibility. It does NOT identify the published
signature S=(S',g') with a Lean StarredWord on arbitrary substructures,
nor assert equality of variable-word-valued Q outputs. Those geometric
and dependent-type signature steps remain.
-/

namespace DualTree.ForwardQFinalFixedSignatureSymbolBridge

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalSignatureCompatibleCoverage

/-- Explicit rooted-symbol data abstracted from the fixed source
signature. The old source roots are retained by the new variable
word h, and on every original f-root before the cut the variables
are identified by their ACTUAL bounded root names. -/
structure FixedEarlySignature
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (h : VariableWord b n α) : Prop where
  oldRoot : ∀ v : g.core.source.word.Vars, v.1 ∈ h.support
  prefixSymbol : ∀ u : g.ambient.Vars,
    ForwardAux u.1.1 g.core.cut →
    CutPreservation.underlyingSymbol h u.1 =
      CutPreservation.underlyingSymbol g.core.source.word u.1

/-- One evaluation of the new word h determines a consistent
evaluation of the old source variables by the SAME root name. -/
def oldAssignment
    {b n l k m : Nat} {α : Type*}
    {g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α}
    {h : VariableWord b n α}
    (H : FixedEarlySignature g h)
    (η : h.Vars → α) :
    g.core.source.word.Vars → α :=
  fun v => η ⟨v.1,H.oldRoot v⟩

/-- Equality of dependent variable-word symbols after erasing
their variable-name proof components implies equality of
evaluations, as long as all old source roots are genuinely
present in the new word. -/
theorem evalSymbol_eq_of_rooted_symbol_eq
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (h : VariableWord b n α)
    (H : FixedEarlySignature g h)
    (η : h.Vars → α)
    (s : BoundedNode b n)
    (heq :
      CutPreservation.underlyingSymbol h s =
      CutPreservation.underlyingSymbol g.core.source.word s) :
    SpanAudit.evalSymbol η (h.word s) =
    SpanAudit.evalSymbol (oldAssignment H η)
      (g.core.source.word.word s) := by
  cases hs : g.core.source.word.word s with
  | inl a =>
      cases ht : h.word s with
      | inl d =>
          have hconst : d = a := by
            have hEq :
                (Sum.inl d : Sum α (BoundedNode b n)) =
                Sum.inl a := by
              simpa [CutPreservation.underlyingSymbol,ht,hs]
                using heq
            exact Sum.inl.inj hEq
          subst d
          rfl
      | inr v =>
          have hEq :
              (Sum.inr v.1 : Sum α (BoundedNode b n)) =
              Sum.inl a := by
            simpa [CutPreservation.underlyingSymbol,ht,hs] using heq
          cases hEq
  | inr v =>
      cases ht : h.word s with
      | inl d =>
          have hEq :
              (Sum.inl d : Sum α (BoundedNode b n)) =
              Sum.inr v.1 := by
            simpa [CutPreservation.underlyingSymbol,ht,hs] using heq
          cases hEq
      | inr w =>
          have hEq :
              (Sum.inr w.1 : Sum α (BoundedNode b n)) =
              Sum.inr v.1 := by
            simpa [CutPreservation.underlyingSymbol,ht,hs] using heq
          have hroot : w.1 = v.1 := Sum.inr.inj hEq
          have hvars :
              w = (⟨v.1,H.oldRoot v⟩ : h.Vars) :=
            Subtype.ext hroot
          simp [SpanAudit.evalSymbol,ht,hs,oldAssignment,hvars]

/-- Every evaluated word in a fixed-root-signature refinement
is compatible with the source substitution on ALL original
ambient f-roots at/before the cut. No two-letter assumption,
Hall matching, or cardinal inequality is used. -/
theorem every_evaluation_is_early_compatible
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (h : VariableWord b n α)
    (H : FixedEarlySignature g h)
    (ψ : TreeWord b n α)
    (hψ : ψ ∈ h.span) :
    EarlyCompatibleValue g ψ := by
  obtain ⟨η,hη⟩ := hψ
  refine ⟨oldAssignment H η,?_⟩
  intro u hu
  have hsource :
      g.core.source.word.word u.1 = g.substitution u := by
    rw [g.source_substitution]
    simp [SpanAudit.substitute,g.ambient.atRoot u]
  have hEq :=
    evalSymbol_eq_of_rooted_symbol_eq
      g h H η u.1 (H.prefixSymbol u hu)
  calc
    ψ u.1 = SpanAudit.evalSymbol η (h.word u.1) :=
      (congrFun hη u.1).symm
    _ = SpanAudit.evalSymbol (oldAssignment H η)
          (g.core.source.word.word u.1) := hEq
    _ = SpanAudit.evalSymbol (oldAssignment H η)
          (g.substitution u) := by rw [hsource]

/-- SOURCE-facing conditional coverage for a full variable-word
refinement h of the final complete-skew word: if h has the old
source's genuine rooted prefix signature, EVERY CONSTANT
evaluation of h has an actual corrected starred Q witness.

The only additional missing step for Definition 26 is the
derivation of these rooted-prefix facts from the literal
starred signature equality sg(h)=S, together with matching
the actual starred Q output object rather than merely its
evaluations. -/
theorem fixed_signature_refinement_evaluations_are_Q_covered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (h : VariableWord b n α)
    (hspan :
      h.span ⊆ (interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (H : FixedEarlySignature g h)
    (ψ : TreeWord b n α) (hψ : ψ ∈ h.span) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ :=
  source_signature_compatible_refinement_covered
    hb g f fallback hq h hspan
    (fun φ hφ => every_evaluation_is_early_compatible g h H φ hφ)
    ψ hψ

end DualTree.ForwardQFinalFixedSignatureSymbolBridge
