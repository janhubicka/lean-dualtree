import DualTree.ForwardQFinalFullSignature

/-!
# Canonical transport of old variable names across equal full signatures

The paper's starred objects carry DEPENDENT variable-root subtypes:
the original source word g' and a later starred output O need not
have definitionally the same Vars type, even when their interior
supports coincide.

The now-verified equality of COMPLETE corrected Definition-26
signatures implies exact equality of interior sets, with the
maximal cut recovered from the partial-word domain.  Therefore
the root-labelled variable types are canonically equivalent,
fixing every underlying bounded root.

We also prove that the old source word and the output word have
IDENTICAL actual symbols on their strict initial signature
segment AFTER renaming those dependent variable types by this
canonical root equivalence.  This moves the validation from
the source-independent "underlyingSymbol" type to the true
VariableWord symbol types.

A future exact Q(w)=O proof must additionally reconstruct the
projected D2 marked points and the late-fibre auxiliary letters.
None of those obligations is silently assumed here.
-/

namespace DualTree.ForwardQFinalFullSignatureRootTransport

open ForwardSourceQTree
open DualTree.ForwardQFinalFullSignature
open DualTree.ForwardQFinalLiteralSignatureTree

/-- The original source and an output with the same true
complete corrected signature have precisely the same
VARIABLE ROOTS, as raw homogeneous-tree nodes. -/
theorem source_output_supportNodes_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (t : Node b) :
    t ∈ g.core.source.word.supportNodes ↔
      t ∈ O.word.supportNodes := by
  have Hliteral := complete_signature_implies_literal hb g O cutO H
  have hinterior :=
    literal_signature_trees_force_same_interior hb g O Hliteral t
  calc
    t ∈ g.core.source.word.supportNodes ↔
        t ∈ SkewTree.interior g.core.source.tree :=
      g.core.source.support_eq_interior t
    _ ↔ t ∈ SkewTree.interior O.tree := hinterior.symm
    _ ↔ t ∈ O.word.supportNodes :=
      (O.support_eq_interior t).symm

/-- An actual old rooted variable corresponds to the same
bounded root in the output dependent variable type, in BOTH
directions. -/
noncomputable def sourceOutputVarsEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO) :
    g.core.source.word.Vars ≃ O.word.Vars := by
  classical
  let toRoot : g.core.source.word.Vars → O.word.Vars := fun v =>
    ⟨v.1, by
      apply ForwardQFinalConcreteSignature.mem_support_of_mem_supportNodes
        O.word v.1
      apply (source_output_supportNodes_iff
        hb g O cutO H v.1.1).1
      change v.1.1 ∈ g.core.source.word.support.map
        (fun x => x.1)
      exact List.mem_map.mpr ⟨v.1,v.2,rfl⟩⟩
  let fromRoot : O.word.Vars → g.core.source.word.Vars := fun v =>
    ⟨v.1, by
      apply ForwardQFinalConcreteSignature.mem_support_of_mem_supportNodes
        g.core.source.word v.1
      apply (source_output_supportNodes_iff
        hb g O cutO H v.1.1).2
      change v.1.1 ∈ O.word.support.map (fun x => x.1)
      exact List.mem_map.mpr ⟨v.1,v.2,rfl⟩⟩
  refine
    { toFun := toRoot
      invFun := fromRoot
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    apply Subtype.ext
    rfl
  · intro v
    apply Subtype.ext
    rfl

/-- The variable correspondence NEVER renames a source
variable to a different ambient node. -/
theorem sourceOutputVarsEquiv_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (v : g.core.source.word.Vars) :
    ((sourceOutputVarsEquiv hb g O cutO H) v).1 = v.1 := rfl

/-- At every old source variable root, the two ACTUAL
dependent VariableWord symbols agree after the canonical
renaming, by their individual atRoot laws. -/
theorem root_reindexed_word_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (v : g.core.source.word.Vars) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (g.core.source.word.word v.1) =
        O.word.word v.1 := by
  let e := sourceOutputVarsEquiv hb g O cutO H
  have hSource := g.core.source.word.atRoot v
  have hTarget := O.word.atRoot (e v)
  have hv : (e v).1 = v.1 :=
    sourceOutputVarsEquiv_root hb g O cutO H v
  change O.word.word v.1 = Sum.inr (e v) at hTarget
  rw [hSource]
  simpa using hTarget.symm

/-- On ALL STRICTLY pre-cut bounded positions, the original and
output dependent word symbols coincide after reindexing variable
names by their shared actual bounded roots.

This upgrades the literal rooted partial-signature equality,
which previously lived only in the erased-root Sum type. -/
theorem strict_prefix_reindexed_word_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (s : BoundedNode b n)
    (hs : ForwardSignatureBoundary.BeforeCut g.core.cut s.1) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (g.core.source.word.word s) = O.word.word s := by
  let e := sourceOutputVarsEquiv hb g O cutO H
  have Hliteral := complete_signature_implies_literal hb g O cutO H
  have hsymbol :
      CutPreservation.underlyingSymbol g.core.source.word s =
        CutPreservation.underlyingSymbol O.word s :=
    (Hliteral.sameStrictPrefix s hs).symm
  cases hS : g.core.source.word.word s with
  | inl a =>
      cases hO : O.word.word s with
      | inl a' =>
          have ha : a = a' := by
            simpa [CutPreservation.underlyingSymbol,hS,hO]
              using hsymbol
          subst a'
          simp [hS,hO]
      | inr v =>
          have hcontr : (Sum.inl a : Sum α (BoundedNode b n)) =
              Sum.inr v.1 := by
            simpa [CutPreservation.underlyingSymbol,hS,hO]
              using hsymbol
          cases hcontr
  | inr v =>
      cases hO : O.word.word s with
      | inl a =>
          have hcontr : (Sum.inr v.1 : Sum α (BoundedNode b n)) =
              Sum.inl a := by
            simpa [CutPreservation.underlyingSymbol,hS,hO]
              using hsymbol
          cases hcontr
      | inr w =>
          have hroot : v.1 = w.1 := by
            have heq : (Sum.inr v.1 : Sum α (BoundedNode b n)) =
                Sum.inr w.1 := by
              simpa [CutPreservation.underlyingSymbol,hS,hO]
                using hsymbol
            exact Sum.inr.inj heq
          have hvar : e v = w := by
            apply Subtype.ext
            exact (sourceOutputVarsEquiv_root hb g O cutO H v).trans hroot
          change (Sum.inr (e v) : Sum α O.word.Vars) = Sum.inr w
          exact congrArg Sum.inr hvar

end DualTree.ForwardQFinalFullSignatureRootTransport
