import DualTree.ForwardQFinalConcreteSignature
import DualTree.ForwardSignatureInteriorExact

/-!
# Literal forward Definition-26 signature tree equality supplies the old interior

The preceding source-facing algebra established that a fixed interior
set and a fixed strict-before-cut rooted prefix word imply Q coverage
of all EVALUATIONS of a starred refinement h in the final f' span.

Now derive the old-interior equality from the genuine corrected
signature-tree construction, rather than making it an independent
hypothesis. The existing, independently verified geometric identity is

  Int(signatureTree(O,cut)) = Int(O.tree) \ {cut}

for an actual starred source word O whose maximal interior is cut.

Therefore any two genuine starred l-variable words O and source
whose corrected signature trees agree AND whose maximal interior
cut is the SAME distinguished node have identical interior sets,
including the cut. Together with equality of their actual strict
prefix words, this yields the concrete rooted-signature certificate
from the previous module and hence evaluated Q coverage.

The remaining substantive tasks are deriving the equal-cut premise
from a chosen unlabelled paper signature (where the cut is recorded
as the last interior) and, crucially, lifting evaluated-word coverage
to equality of the FULL STARRED VARIABLE-WORD Q outputs and skeletons.
The printed reverse-order auxiliary convention is still separate.
-/

namespace DualTree.ForwardQFinalLiteralSignatureTree

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open DualTree.ForwardQFinalConcreteSignature

/-- Genuine equality of forward-corrected Definition-26 signatures
for two starred words, expressed at their COMMON maximal interior cut.
The tree is the exact first-boundary signatureTree_at_maxInterior,
not an invented interior-only signature skeleton. -/
structure SameLiteralForwardSignature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop where
  cutInterior : g.core.cut ∈ SkewTree.interior O.tree
  cutMaximal : ∀ t, t ∈ SkewTree.interior O.tree →
    SkewTree.forwardAuxB t g.core.cut = true
  sameSignatureTree :
    ForwardStarredSignature.signatureTree_at_maxInterior
      hb O g.core.cut cutInterior cutMaximal =
    ForwardStarredSignature.signatureTree_at_maxInterior
      hb g.core.source g.core.cut g.core.hcut g.core.hmax
  sameStrictPrefix : ∀ s : BoundedNode b n,
    ForwardSignatureBoundary.BeforeCut g.core.cut s.1 →
      CutPreservation.underlyingSymbol O.word s =
      CutPreservation.underlyingSymbol g.core.source.word s

/-- The EXACT constructed signature-tree equality, with the same
last interior cut, implies equality of the old and new starred
interior sets. This uses the verified interior-minus-cut identity
twice, and treats membership of the cut separately. -/
theorem literal_signature_trees_force_same_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (t : Node b) :
    t ∈ SkewTree.interior O.tree ↔
      t ∈ SkewTree.interior g.core.source.tree := by
  have hOutO :=
    ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
      hb O g.core.cut H.cutInterior H.cutMaximal
  have hOutS :=
    ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
      hb g.core.source g.core.cut g.core.hcut g.core.hmax
  have hiO :
      t ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree_at_maxInterior
          hb O g.core.cut H.cutInterior H.cutMaximal) ↔
      t ∈ SkewTree.interior O.tree ∧ t ≠ g.core.cut := by
    exact ForwardSignatureInteriorExact.signature_interior_iff_original_ne_cut
      O g.core.cut H.cutInterior H.cutMaximal hOutO t
  have hiS :
      t ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree_at_maxInterior
          hb g.core.source g.core.cut g.core.hcut g.core.hmax) ↔
      t ∈ SkewTree.interior g.core.source.tree ∧ t ≠ g.core.cut := by
    exact ForwardSignatureInteriorExact.signature_interior_iff_original_ne_cut
      g.core.source g.core.cut g.core.hcut g.core.hmax hOutS t
  constructor
  · intro ht
    by_cases hc : t = g.core.cut
    · simpa only [hc] using g.core.hcut
    · have hinSignature := hiO.mpr ⟨ht,hc⟩
      rw [H.sameSignatureTree] at hinSignature
      exact (hiS.mp hinSignature).1
  · intro ht
    by_cases hc : t = g.core.cut
    · simpa only [hc] using H.cutInterior
    · have hinSignature := hiS.mpr ⟨ht,hc⟩
      rw [← H.sameSignatureTree] at hinSignature
      exact (hiO.mp hinSignature).1

/-- Literal corrected signature-tree/strict-prefix agreement,
at the same last interior cut, is enough to supply the
FULL ConcreteForwardSignature certificate (including the cut). -/
theorem literal_signature_implies_concrete_signature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O) :
    ConcreteForwardSignature g O := by
  refine ⟨?_, H.sameStrictPrefix⟩
  intro t
  exact literal_signature_trees_force_same_interior hb g O H t

/-- Any starred l-variable-word refinement with this LITERAL
forward-corrected Definition-26 signature has ALL its constant
evaluations covered by true corrected starred Q images, provided
the starred word refines the constructed complete-skew f' span.

This theorem removes the previously independent same-interior
hypothesis. It does NOT yet produce Q(w) equal to the starred
word itself as a dependent variable-word object. -/
theorem literal_signature_refinement_evaluations_covered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hq : 0 < q)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hspan :
      O.word.span ⊆
        (interpolatedFinalWord
          g f (fun a : α => a) fallback).span)
    (H : SameLiteralForwardSignature hb g O)
    (ψ : TreeWord b n α)
    (hψ : ψ ∈ O.word.span) :
    ∃ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback)
      (τ : g.core.source.word.Vars → α),
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).word.eval τ = ψ :=
  concrete_signature_refinement_evaluations_covered
    hb g f fallback hq O hspan
    (literal_signature_implies_concrete_signature hb g O H)
    ψ hψ

end DualTree.ForwardQFinalLiteralSignatureTree
