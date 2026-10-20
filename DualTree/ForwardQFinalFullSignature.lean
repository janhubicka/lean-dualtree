import DualTree.ForwardQFinalLiteralSignatureTree
import DualTree.ForwardSignatureCutDomainRigidity

/-!
# A complete corrected signature determines its own maximal interior cut

The genuine forward-corrected Definition 26 signature consists of the
literal finite first-boundary signature tree, together with a PARTIAL
root-labelled word on the strict forward-initial domain before the
maximal interior cut.  That partial map records its domain.  Equality
of bare values only on an unspecified intersection would not suffice.

We model the partial word as an Option-valued map on the ACTUAL common
bounded homogeneous-tree index type.  Equality of these maps identifies
the cuts by the already kernel-verified strict-domain rigidity lemma.
Consequently equality of the complete corrected signatures implies
the exact common-cut signature certificate proved previously, which
in turn covers every evaluation of a starred refinement of the final
word by a genuine corrected starred Q output.

The conclusion concerns EVALUATED words and the corrected forward
auxiliary order.  It does NOT assert equality of variable-word-valued
Q outputs or equivalence with the published reverse auxiliary order.
-/

namespace DualTree.ForwardQFinalFullSignature

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open DualTree.ForwardQFinalLiteralSignatureTree

/-- The actual strict-prefix rooted signature word, including its
domain of definition.  Option.none is not an alphabet symbol:
it means the bounded position lies outside the strict initial cut. -/
noncomputable def strictPartialWord
    {b n : Nat} {α : Type*}
    (cut : Node b) (h : VariableWord b n α)
    (s : BoundedNode b n) :
    Option (Sum α (BoundedNode b n)) := by
  classical
  exact if ForwardSignatureBoundary.BeforeCut cut s.1 then
    some (CutPreservation.underlyingSymbol h s)
  else none

/-- Definedness of the literal partial signature word is
EXACTLY membership in the strict forward-initial domain. -/
theorem strictPartialWord_ne_none_iff
    {b n : Nat} {α : Type*}
    (cut : Node b) (h : VariableWord b n α)
    (s : BoundedNode b n) :
    strictPartialWord cut h s ≠ none ↔
      ForwardSignatureBoundary.BeforeCut cut s.1 := by
  classical
  by_cases hs : ForwardSignatureBoundary.BeforeCut cut s.1
  · simp [strictPartialWord, hs]
  · simp [strictPartialWord, hs]

/-- The concrete ordered PAIR making up the corrected literal
Definition-26 signature: first-boundary tree and optional rooted
partial word.  The latter includes the restricted word's domain. -/
noncomputable def completeSignature
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true) :
    List (Node b) ×
      (BoundedNode b n → Option (Sum α (BoundedNode b n))) :=
  (ForwardStarredSignature.signatureTree_at_maxInterior
      hb O cut hcut hmax,
    strictPartialWord cut O.word)

/-- Equality of the ACTUAL two-part corrected signatures
without postulating that their (a priori different) last
interior cuts are equal. -/
structure SameCompleteForwardSignature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b) : Prop where
  cutInterior : cutO ∈ SkewTree.interior O.tree
  cutMaximal : ∀ t, t ∈ SkewTree.interior O.tree →
    SkewTree.forwardAuxB t cutO = true
  signatureEq :
    completeSignature hb O cutO cutInterior cutMaximal =
      completeSignature hb g.core.source g.core.cut
        g.core.hcut g.core.hmax

/-- Equality of true bounded partial signature-word domains
forces the TWO maximal interior cuts to coincide.  In particular
a shared cut is a consequence, not an additional manuscript axiom. -/
theorem complete_signature_forces_same_cut
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO) :
    cutO = g.core.cut := by
  have hPartial :
      strictPartialWord cutO O.word =
        strictPartialWord g.core.cut g.core.source.word := by
    exact congrArg Prod.snd H.signatureEq
  have hDomain :
      ∀ s : BoundedNode b n,
        ForwardSignatureBoundary.BeforeCut cutO s.1 ↔
          ForwardSignatureBoundary.BeforeCut g.core.cut s.1 := by
    intro s
    have heq := congrFun hPartial s
    constructor
    · intro hs
      have hleft : strictPartialWord cutO O.word s ≠ none :=
        (strictPartialWord_ne_none_iff cutO O.word s).2 hs
      have hright :
          strictPartialWord g.core.cut g.core.source.word s ≠ none := by
        rw [← heq]
        exact hleft
      exact (strictPartialWord_ne_none_iff
        g.core.cut g.core.source.word s).1 hright
    · intro hs
      have hright :
          strictPartialWord g.core.cut g.core.source.word s ≠ none :=
        (strictPartialWord_ne_none_iff
          g.core.cut g.core.source.word s).2 hs
      have hleft : strictPartialWord cutO O.word s ≠ none := by
        rw [heq]
        exact hright
      exact (strictPartialWord_ne_none_iff cutO O.word s).1 hleft
  have hcutOtree : cutO ∈ O.tree :=
    (List.mem_filter.mp H.cutInterior).1
  let outCut : BoundedNode b n :=
    ⟨cutO, O.tree_bounded cutO hcutOtree⟩
  let oldCut : BoundedNode b n :=
    ⟨g.core.cut, g.T_bounded g.core.cut g.core.hcutT⟩
  have hEq :
      outCut = oldCut :=
    ForwardSignatureCutDomainRigidity.bounded_cut_eq_of_beforeCut_iff
      outCut oldCut hDomain
  exact congrArg Subtype.val hEq

/-- Complete corrected signature equality, including the strict
partial-word DOMAIN, implies the already proved literal-signature
certificate with the common cut and correct rooted symbols. -/
theorem complete_signature_implies_literal
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO) :
    SameLiteralForwardSignature hb g O := by
  have hEqCut := complete_signature_forces_same_cut hb g O cutO H
  subst cutO
  have hTree :
      ForwardStarredSignature.signatureTree_at_maxInterior
        hb O g.core.cut H.cutInterior H.cutMaximal =
      ForwardStarredSignature.signatureTree_at_maxInterior
        hb g.core.source g.core.cut g.core.hcut g.core.hmax := by
    exact congrArg Prod.fst H.signatureEq
  have hPartial :
      strictPartialWord g.core.cut O.word =
        strictPartialWord g.core.cut g.core.source.word := by
    exact congrArg Prod.snd H.signatureEq
  refine
    { cutInterior := H.cutInterior
      cutMaximal := H.cutMaximal
      sameSignatureTree := hTree
      sameStrictPrefix := ?_ }
  intro s hs
  have heq := congrFun hPartial s
  have hsome :
      some (CutPreservation.underlyingSymbol O.word s) =
        some (CutPreservation.underlyingSymbol
          g.core.source.word s) := by
    simpa [strictPartialWord, hs] using heq
  exact Option.some.inj hsome

/-- Every evaluated word of an ACTUAL forward-signature-fixed starred
refinement of the completed final variable word has a genuine
corrected starred Q witness.  Neither same-cut nor same-interior
is independently assumed: both are forced by complete signature
equality.  The conclusion is still about EVALUATIONS, not full
starred-word Q-object equality. -/
theorem complete_signature_refinement_evaluations_covered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (hspan :
      O.word.span ⊆
        (interpolatedFinalWord
          g f (fun a : α => a) fallback).span)
    (H : SameCompleteForwardSignature hb g O cutO)
    (ψ : TreeWord b n α)
    (hψ : ψ ∈ O.word.span) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ :=
  literal_signature_refinement_evaluations_covered
    hb g f fallback hq O hspan
    (complete_signature_implies_literal hb g O cutO H)
    ψ hψ

end DualTree.ForwardQFinalFullSignature
