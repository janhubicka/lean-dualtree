import DualTree.ForwardQVisibleRootCapacity

/-!
# A typed inverse to the corrected Q auxiliary decoder on visible roots

At a fixed genuine sorted outside-cut frontier i, the corrected
Q map has m+1 auxiliary alphabet labels.  Its verified decoder
R_i reaches every original source variable whose ACTUAL root is
a strict complete-T predecessor of the frontier.

This file turns that existential decoder theorem into a named
encoder for precisely the visible roots.  It is an entirely
root-faithful map from each visible source variable to one of
the finite auxiliary labels, with a checked right-inverse law.

The construction is extended to original alphabet constants
alongside visible source variables.  No Hall injection across
different frontiers is needed: this encoder is only a RIGHT
inverse of the per-frontier decoder, and the old variables
are already dependent names rooted at their actual nodes.

The important unproved NEXT step is to show that every source
variable appearing in a late f-fibre of the requested starred
output O is actually a strict predecessor of its selected
frontier.  This module does not assume or claim that visibility,
nor does it construct the whole mixed input realizing O.
-/

namespace DualTree.ForwardQVisibleAuxSymbolEncoder

open ForwardSourceQTree

/-- A genuine old source-variable root which is a strict
complete-T predecessor of a sorted outside-cut frontier is
an element of the ACTUAL visible ancestor list for that
frontier.  This is a set-level membership proof, not a
cardinality or guessed coding map. -/
theorem source_var_visible_of_strict_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c)
    (v : c.source.word.Vars)
    (hpre : IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt
        c.T c.cut i).1) :
    v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i := by
  have hT : v.1.1 ∈ c.T :=
    ForwardQConeVariableVisibility.sourceRoot_mem_T c v
  have hvar : v.1.1 ∈ c.source.word.supportNodes := by
    change v.1.1 ∈ c.source.word.support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨v.1,v.2,rfl⟩
  unfold ForwardQVisibleAncestorDecoder.visibleList
    Lemma27Repair.visibleAncestors
  apply List.mem_filter.mpr
  constructor
  · unfold SkewTree.preds
    apply List.mem_filter.mpr
    exact ⟨hT,
      (SkewBranchGeometry.strictPrefixB_iff
        v.1.1
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1).2 hpre⟩
  · simpa using hvar

/-- The m+1 auxiliary labels can encode EVERY genuine old
source variable which is strictly above this one frontier,
without any additional individual capacity hypothesis. -/
theorem exists_aux_label_for_visible_source_var
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (v : c.source.word.Vars)
    (hpre : IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1) :
    ∃ j : Fin (m + 1),
      ForwardQVisibleAncestorDecoder.decodeAux
        c fallback i j = Sum.inr v :=
  ForwardQVisibleRootCapacity.decodeAux_onto_every_visible_variable
    c fallback i v
    (source_var_visible_of_strict_prefix c i v hpre)

/-- Select one TRUE existing auxiliary label for a visible
source variable; it is never allocated outside Fin(m+1). -/
noncomputable def encodeVisibleSourceVar
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (v : c.source.word.Vars)
    (hpre : IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1) :
    Fin (m + 1) :=
  Classical.choose
    (exists_aux_label_for_visible_source_var
      c fallback i v hpre)

/-- The encoder is a genuine RIGHT inverse of the actual
per-frontier Q decoder at every visible old source variable. -/
theorem decodeAux_encodeVisibleSourceVar
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (v : c.source.word.Vars)
    (hpre : IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1) :
    ForwardQVisibleAncestorDecoder.decodeAux
      c fallback i (encodeVisibleSourceVar c fallback i v hpre) =
        Sum.inr v :=
  Classical.choose_spec
    (exists_aux_label_for_visible_source_var
      c fallback i v hpre)

/-- The letters which can be represented by the literal
enlarged alphabet in the i-th frontier: every original letter
and every old source variable STRICTLY visible there. -/
abbrev VisibleSymbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c) :=
  Sum α {v : c.source.word.Vars //
    IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1}

/-- Encode a visible dependent symbol into the ACTUAL enlarged
letter type alpha + Fin(m+1), without confusing old source
variables with independent post-Ramsey local variable names. -/
noncomputable def encodeVisibleSymbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c) :
    VisibleSymbol c i → Sum α (Fin (m + 1))
  | Sum.inl a => Sum.inl a
  | Sum.inr v =>
      Sum.inr
        (encodeVisibleSourceVar c fallback i v.1 v.2)

/-- Decoding an encoded genuinely visible symbol yields its
original alpha constant or its true original source variable
name, with no renaming or loss of information. -/
theorem decode_encoded_visible_symbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (s : VisibleSymbol c i) :
    (match encodeVisibleSymbol c fallback i s with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux c fallback i j) =
      Sum.map id Subtype.val s := by
  cases s with
  | inl a =>
      rfl
  | inr v =>
      simpa [encodeVisibleSymbol] using
        (decodeAux_encodeVisibleSourceVar
          c fallback i v.1 v.2)

end DualTree.ForwardQVisibleAuxSymbolEncoder
