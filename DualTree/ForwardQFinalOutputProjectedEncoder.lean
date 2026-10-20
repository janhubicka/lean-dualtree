import DualTree.ForwardQFinalFullSignatureRootTransport
import DualTree.ForwardQFinalProjectedOldVariableVisible
import DualTree.ForwardQAmbientFibreSymbol

/-!
# Exact local encoding of symbols in a same-signature starred output

A starred output with the same actual complete corrected signature as
the source has a canonical root-preserving equivalence of dependent
variable types.  At a projected coordinate P_i(z), the word's
below-root law forces any output variable symbol to name an old
source root strictly preceding frontier i.  The verified R_i decoder
therefore has a genuine auxiliary letter realizing that symbol.

The result constructs and certifies only the ordinary enlarged
coordinate LETTERS.  It makes no claim about the marked D2 points,
starred-order constraints, whole-object Q surjectivity, or the
remaining Ramsey span step.
-/

namespace DualTree.ForwardQFinalOutputProjectedEncoder

open ForwardSourceQTree
open ForwardQFinalFullSignature
open ForwardQFinalFullSignatureRootTransport

/-- The actual variable symbol of O at a genuine projected position
belongs to an old source root strictly preceding the same frontier.
The old/output equivalence fixes underlying bounded root nodes. -/
theorem output_variable_strictly_visible_at_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1)))
    (v : O.word.Vars)
    (hv :
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) = Sum.inr v) :
    IsStrictPrefix
      ((sourceOutputVarsEquiv hb g O cutO H).symm v).1.1
      (ForwardOrderedProjections.frontierAt
        g.core.T g.core.cut i).1 := by
  let e := sourceOutputVarsEquiv hb g O cutO H
  let u : g.core.source.word.Vars := e.symm v
  have hroot : u.1 = v.1 := by
    calc
      u.1 = (e u).1 :=
        (sourceOutputVarsEquiv_root hb g O cutO H u).symm
      _ = v.1 := congrArg Subtype.val (e.apply_symm_apply v)
  have hbelow : IsPrefix v.1.1
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z).1 :=
    O.word.below v _ hv
  have hpre : IsPrefix u.1.1
      (ForwardQFinalRefinementRoots.projected
        g.core ⟨i, z⟩).1 := by
    change IsPrefix u.1.1
      (ForwardQActualCoordinateWord.projectLocal g.core i z).1
    change IsPrefix v.1.1
      (ForwardQActualCoordinateWord.projectLocal g.core i z).1 at hbelow
    rw [hroot]
    exact hbelow
  exact ForwardQFinalProjectedOldVariableVisible.old_variable_prefix_frontier_of_projected
    g.core i z u hpre

/-- The exact OUTPUT symbol at a projected coordinate is the decoded
value of some letter from the genuine enlarged alphabet alpha + Fin(m+1).
There is no capacity hypothesis beyond those in the original frame. -/
theorem exists_encoded_projected_output_symbol
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    ∃ a : Sum α (Fin (m + 1)),
      Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
        (match a with
          | Sum.inl x => (Sum.inl x : Sum α g.core.source.word.Vars)
          | Sum.inr j =>
              ForwardQVisibleAncestorDecoder.decodeAux
                g.core fallback i j) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) := by
  let p := ForwardQActualCoordinateWord.projectedBounded
    g.core g.T_bounded i z
  let e := sourceOutputVarsEquiv hb g O cutO H
  cases hv : O.word.word p with
  | inl a =>
      refine ⟨Sum.inl a, ?_⟩
      rfl
  | inr v =>
      let u : g.core.source.word.Vars := e.symm v
      have hstrict : IsStrictPrefix u.1.1
          (ForwardOrderedProjections.frontierAt
            g.core.T g.core.cut i).1 :=
        output_variable_strictly_visible_at_projected
          hb g O cutO H i z v hv
      obtain ⟨j, hj⟩ :=
        ForwardQVisibleAuxSymbolEncoder.exists_aux_label_for_visible_source_var
          g.core fallback i u hstrict
      refine ⟨Sum.inr j, ?_⟩
      change Sum.map id e
        (ForwardQVisibleAncestorDecoder.decodeAux
          g.core fallback i j) = Sum.inr v
      calc
        Sum.map id e
          (ForwardQVisibleAncestorDecoder.decodeAux
            g.core fallback i j) =
            Sum.map id e (Sum.inr u) := congrArg (Sum.map id e) hj
        _ = Sum.inr v := by
          simpa only [Sum.map_inr] using
            congrArg (Sum.inr : O.word.Vars → Sum α O.word.Vars)
              (e.apply_symm_apply v)

/-- Choose a local enlarged letter realizing the output symbol at
the genuine projected coordinate.  The decoder certification below
makes the classical choice independent of further combinatorial work. -/
noncomputable def encodeProjectedOutputSymbol
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    Sum α (Fin (m + 1)) :=
  Classical.choose
    (exists_encoded_projected_output_symbol
      hb g O cutO H fallback i z)

/-- At every projected local coordinate, decoding the chosen
enlarged letter gives EXACTLY the output's dependent variable-word
symbol after transport along the canonical same-root equivalence. -/
theorem decoded_encoded_projected_output_symbol
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (match encodeProjectedOutputSymbol
        hb g O cutO H fallback i z with
        | Sum.inl x => (Sum.inl x : Sum α g.core.source.word.Vars)
        | Sum.inr j =>
            ForwardQVisibleAncestorDecoder.decodeAux
              g.core fallback i j) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) :=
  Classical.choose_spec
    (exists_encoded_projected_output_symbol
      hb g O cutO H fallback i z)


/-- Replace ordinary enlarged letters by certified encodings of the
starred-output symbols at the actual projected coordinates.  Preserve
both sorts of marked points from the existing mixed-product input. -/
noncomputable def reletterInputFromOutput
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core) :
    ForwardQEnlargedConstantWords.EnlargedInput g.core where
  words := encodeProjectedOutputSymbol hb g O cutO H fallback
  upPoint := base.upPoint
  bulletPoint := base.bulletPoint

/-- The genuine D2 markers are not reselected or reindexed. -/
theorem reletterInput_bulletPoint_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (reletterInputFromOutput hb g O cutO H fallback base).bulletPoint i =
      base.bulletPoint i :=
  rfl

/-- Corrected W_* membership depends exclusively on the original
marked D2 points, so changing all enlarged ordinary word letters
does not disturb the already certified selected D2 order. -/
theorem reletterInput_preserves_IsStarred
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (hstar : ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback base)) :
    ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (reletterInputFromOutput hb g O cutO H fallback base)) := by
  exact hstar

/-- Relettering preserves the marked geometry while now making the
ACTUAL source-facing Q symbol agree with the requested output symbol
at every true projected original-f root, after canonical reindexing
of the old/output dependent variable types. -/
theorem reletterInput_Q_matches_output_at_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (i : ForwardQFullFrontierWord.Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (reletterInputFromOutput hb g O cutO H fallback base)
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z)) =
      O.word.word
        (ForwardQActualCoordinateWord.projectedBounded
          g.core g.T_bounded i z) := by
  let w := reletterInputFromOutput hb g O cutO H fallback base
  have hroot :
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (ForwardQActualCoordinateWord.projectLocal g.core i z).1
        (ForwardQActualCoordinateWord.projectLocal g.core i z).2).1 =
      ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z := by
    apply Subtype.ext
    rfl
  have hQ := ForwardQAmbientFibreSymbol.fibreQ_projected_root
    g fallback w i z
  rw [hroot] at hQ
  have hW :
      w.words i z = encodeProjectedOutputSymbol
        hb g O cutO H fallback i z := rfl
  rw [hW] at hQ
  exact (congrArg
    (Sum.map id (sourceOutputVarsEquiv hb g O cutO H)) hQ).trans
    (decoded_encoded_projected_output_symbol
      hb g O cutO H fallback i z)

/-- Transport any already legal corrected-starred D2 markers to the
chosen ordinary alphabet words; this is not a choice of new D2 markers. -/
noncomputable def reletterStarredFromOutput
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (base : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback) :
    ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback :=
  ⟨reletterInputFromOutput hb g O cutO H fallback base.1,
    reletterInput_preserves_IsStarred
      hb g O cutO H fallback base.1 base.2⟩

end DualTree.ForwardQFinalOutputProjectedEncoder
