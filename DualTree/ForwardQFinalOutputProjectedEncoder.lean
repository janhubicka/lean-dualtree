import DualTree.ForwardQFinalFullSignatureRootTransport
import DualTree.ForwardQFinalProjectedOldVariableVisible

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
    simpa only [hroot] using hbelow
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
      simpa only [Sum.map_inl] using hv.symm
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
          g.core fallback i j) = O.word.word p
      calc
        Sum.map id e
          (ForwardQVisibleAncestorDecoder.decodeAux
            g.core fallback i j) =
            Sum.map id e (Sum.inr u) := congrArg (Sum.map id e) hj
        _ = Sum.inr v := by
          simpa only [Sum.map_inr] using
            congrArg (Sum.inr : O.word.Vars → Sum α O.word.Vars)
              (e.apply_symm_apply v)
        _ = O.word.word p := hv.symm

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

end DualTree.ForwardQFinalOutputProjectedEncoder
