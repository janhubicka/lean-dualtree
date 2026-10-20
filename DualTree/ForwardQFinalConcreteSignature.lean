import DualTree.ForwardQFinalFixedSignatureSymbolBridge
import DualTree.ForwardSignatureBoundary

/-!
# Actual fixed source interior and strict-forward-prefix word yield early Q compatibility

Definition 26 of the paper attaches to each starred l-variable word a
signature whose tree records the source interior and boundary and whose
word is restricted to the STRICT auxiliary initial segment before the
last interior cut. The cut itself is an interior variable root, even
though the restricted prefix-word domain excludes it.

For the corrected forward auxiliary order, the two direct fixed-
signature components are:
 (1) equality of the interiors of the starred output and the source;
 (2) equality of the underlying rooted variable symbols at all bounded
     positions strictly before the corrected cut.

The first condition ensures all old source variables are present in
the output at the SAME bounded tree positions. The second is already
the fixed partial-word condition of the signature. At the cut, where
the partial prefix does not apply, both words emit the identical
root-labelled variable by their atRoot axiom.

Therefore these two concrete source-side signature conditions imply
the FixedEarlySignature algebraic certificate of the preceding module,
which in turn covers evaluations of every such final-span refinement
by genuine corrected starred Q images.

Proving that equality of the LITERAL constructed signature trees S'
implies equality of their interiors, and upgrading to an equality of
starred VARIABLE-WORD Q outputs, remain separate source-facing steps.
The printed reverse-order signature is not silently modified.
-/

namespace DualTree.ForwardQFinalConcreteSignature

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalFixedSignatureSymbolBridge

/-- A bounded root belongs to the support list iff its raw node
belongs to the corresponding list of supportNodes. -/
theorem mem_support_of_mem_supportNodes
    {b n : Nat} {α : Type*}
    (h : VariableWord b n α)
    (u : BoundedNode b n)
    (hu : u.1 ∈ h.supportNodes) :
    u ∈ h.support := by
  change u.1 ∈ h.support.map (fun v => v.1) at hu
  obtain ⟨v,hv,heq⟩ := List.mem_map.mp hu
  have hval : v = u := Subtype.ext heq
  simpa only [hval] using hv

/-- The two exact rooted components of an abstract forward
fixed signature: the source interior nodes and the strictly
forward-before-cut partial word in the same bounded alphabet.
No arbitrary pre-cut evaluation choices are introduced. -/
structure ConcreteForwardSignature
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop where
  sameInterior : ∀ t : Node b,
    t ∈ SkewTree.interior O.tree ↔
      t ∈ SkewTree.interior g.core.source.tree
  sameStrictPrefix : ∀ s : BoundedNode b n,
    ForwardSignatureBoundary.BeforeCut g.core.cut s.1 →
      CutPreservation.underlyingSymbol O.word s =
      CutPreservation.underlyingSymbol g.core.source.word s

/-- Old source-variable roots remain actual output variable roots,
as a consequence of equality of the source and output INTERIORS.
The proof does not assume support-list ordering agrees. -/
theorem original_root_mem_output
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : ConcreteForwardSignature g O)
    (v : g.core.source.word.Vars) :
    v.1 ∈ O.word.support := by
  have hsource : v.1.1 ∈ g.core.source.word.supportNodes := by
    change v.1.1 ∈ g.core.source.word.support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨v.1,v.2,rfl⟩
  have hinterior : v.1.1 ∈ SkewTree.interior O.tree :=
    (H.sameInterior v.1.1).2
      ((g.core.source.support_eq_interior v.1.1).1 hsource)
  have hout : v.1.1 ∈ O.word.supportNodes :=
    (O.support_eq_interior v.1.1).2 hinterior
  exact mem_support_of_mem_supportNodes O.word v.1 hout

/-- At the last source interior root cut, both words must emit
the SAME root-labelled variable, even though the signature's
strict prefix-word domain does not include that cut. -/
theorem same_cut_root_symbol
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : ConcreteForwardSignature g O)
    (u : g.ambient.Vars)
    (hcut : u.1.1 = g.core.cut) :
    CutPreservation.underlyingSymbol O.word u.1 =
      CutPreservation.underlyingSymbol g.core.source.word u.1 := by
  have hsource : u.1.1 ∈ g.core.source.word.supportNodes :=
    (g.core.source.support_eq_interior u.1.1).2
      (by simpa only [hcut] using g.core.hcut)
  have hO : u.1 ∈ O.word.support :=
    mem_support_of_mem_supportNodes O.word u.1
      ((O.support_eq_interior u.1.1).2
        ((H.sameInterior u.1.1).2
          ((g.core.source.support_eq_interior u.1.1).1 hsource)))
  have hS : u.1 ∈ g.core.source.word.support :=
    mem_support_of_mem_supportNodes g.core.source.word u.1 hsource
  have hOroot :
      O.word.word u.1 = Sum.inr
        (⟨u.1,hO⟩ : O.word.Vars) :=
    O.word.atRoot ⟨u.1,hO⟩
  have hSroot :
      g.core.source.word.word u.1 = Sum.inr
        (⟨u.1,hS⟩ : g.core.source.word.Vars) :=
    g.core.source.word.atRoot ⟨u.1,hS⟩
  simp [CutPreservation.underlyingSymbol,hOroot,hSroot]

/-- Concrete equality of the actual strict signature prefix,
plus shared interiors, implies equality of rooted symbols at
EVERY original ambient f-variable root at/before the cut. -/
theorem concrete_signature_to_fixed_early
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : ConcreteForwardSignature g O) :
    FixedEarlySignature g O.word := by
  refine ⟨original_root_mem_output g O H, ?_⟩
  intro u hu
  by_cases hc : u.1.1 = g.core.cut
  · exact same_cut_root_symbol g O H u hc
  · exact H.sameStrictPrefix u.1 ⟨hu,hc⟩

/-- If an actual starred l-variable-word output has the two
concrete fixed-signature components and its evaluated span
refines the final complete-skew f', then EVERY evaluation of
that starred output admits a genuine corrected starred Q
witness. This is a source-facing consequence of all the
previously verified Q/ambient-fibre geometry. -/
theorem concrete_signature_refinement_evaluations_covered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hspan :
      O.word.span ⊆ (interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (H : ConcreteForwardSignature g O)
    (ψ : TreeWord b n α)
    (hψ : ψ ∈ O.word.span) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ :=
  fixed_signature_refinement_evaluations_are_Q_covered
    hb g f fallback hq O.word hspan
    (concrete_signature_to_fixed_early g O H) ψ hψ

end DualTree.ForwardQFinalConcreteSignature
