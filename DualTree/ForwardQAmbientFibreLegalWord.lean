import DualTree.ForwardQAmbientFibreSymbol

/-!
# Package the FULL corrected fibrewise Q as a legal starred word

The paper's Q-symbol map has now been defined from the actual ambient
f-variable fibres, not from the ambient positions' geometric cones.
This module closes its remaining variable-word well-formedness check:
  * at every old source root v, the Q symbol is that same variable v;
  * EVERY emitted old-source variable has its root as a prefix
    of the whole original ambient position s;
  * this holds also in late f-fibres, because visible-ancestor
    decoder roots are strict prefixes of their selected frontier,
    the frontier precedes the original f ROOT, and the original
    f root precedes every member of its own fibre.

Thus the original source variable-root support and the fully
fibrewise Q symbol form a genuine VariableWord, not a placeholder
or a partially decoded map. Combining this new word with the
previously proved corrected semi-complete Q skeleton gives an actual
legal StarredSignature.StarredWord on the true projected support.

The source-facing theorem for printed Q(iv) on ENTIRE f-fibres
then transfers verbatim to the final word, not just its symbol
scaffold. No independent-variable Hall premise is required.

Important remaining caveats: the FULL ambient frame assumes a
uniform syntactic refinement g' = f[rho] (not implied by evaluated
span containment for singleton alphabets); the geometric Q support
is in the repaired forward order, not the paper's printed order.
Simple-colouring pullback and construction of the final f' remain
separate, unproved obligations, so this does not prove Lemma 27.
-/

namespace DualTree.ForwardQAmbientFibreLegalWord

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol

/-- If the R_i decoder emits an old source variable at an
actual original ambient f-root, its old variable root MUST
be an ambient prefix of that f-root. The chain is:
old root ⊏ selected frontier ⊑ original ambient f-root. -/
theorem decodeAmbientRoot_below
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars)
    (old : c.core.source.word.Vars)
    (hdec : decodeAmbientRoot c fallback w v = Sum.inr old) :
    IsPrefix old.1.1 v.1.1 := by
  cases hsel :
    ForwardQFullFrontierWord.selectedFrontier c.core v.1 with
  | none =>
      simp [decodeAmbientRoot, hsel] at hdec
  | some i =>
      cases hletter :
        ForwardQEnlargedConstantWords.sampledEnlarged
          c.core w fallback i v.1 with
      | inl a =>
          simp [decodeAmbientRoot, hsel, hletter] at hdec
      | inr j =>
          have hdecoder :
              ForwardQVisibleAncestorDecoder.decodeAux
                c.core fallback i j = Sum.inr old := by
            simpa [decodeAmbientRoot, hsel, hletter] using hdec
          have hancestor :
              IsPrefix old.1.1
                (ForwardOrderedProjections.frontierAt
                  c.core.T c.core.cut i).1 :=
            (ForwardQVisibleAncestorDecoder.decodeAux_variable_prefix
              c.core fallback i j old hdecoder).1
          have hfrontier :
              IsPrefix
                (ForwardOrderedProjections.frontierAt
                  c.core.T c.core.cut i).1 v.1.1 :=
            selectedFrontier_some_prefix c.core v.1 i hsel
          exact isPrefix_trans hancestor hfrontier

/-- Every old variable emitted by the genuinely fibrewise
corrected Q symbol is rooted below the ENTIRE original ambient
position. For early fibres use g'. For late fibres compose
old-root/frontier, frontier/f-root, f-root/position prefixes. -/
theorem fibreQ_symbol_below
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (old : c.core.source.word.Vars)
    (s : BoundedNode b n)
    (h : fibreQSymbol c fallback w s = Sum.inr old) :
    IsPrefix old.1.1 s.1 := by
  cases hf : c.ambient.word s with
  | inl a =>
      simp [fibreQSymbol, hf] at h
  | inr v =>
      by_cases hbefore : ForwardAux v.1.1 c.core.cut
      · have hsource :
            c.core.source.word.word s = Sum.inr old := by
          simpa [fibreQSymbol, hf, hbefore] using h
        exact c.core.source.word.below old s hsource
      · have hdecoded :
            decodeAmbientRoot c fallback w v =
              Sum.inr old := by
          simpa [fibreQSymbol, hf, hbefore] using h
        have hroot : IsPrefix old.1.1 v.1.1 :=
          decodeAmbientRoot_below c fallback w v old hdecoded
        have hposition : IsPrefix v.1.1 s.1 :=
          c.ambient.below v s hf
        exact isPrefix_trans hroot hposition

/-- The genuine WHOLE-domain Q map is a legal variable word.
Its variable-root list is precisely the source's original
interior roots; no dummy or unmatched cone-variable names. -/
noncomputable def fibreQVariableWord
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core) :
    DualTree.VariableWord b n α where
  support := c.core.source.word.support
  support_nodup := c.core.source.word.support_nodup
  word := fibreQSymbol c fallback w
  atRoot := by
    intro v
    exact fibreQ_at_old_root c fallback w v
  below := by
    intro v s h
    exact fibreQ_symbol_below c fallback w v s h

theorem fibreQVariableWord_support
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core) :
    (fibreQVariableWord c fallback w).support =
      c.core.source.word.support :=
  rfl

theorem fibreQVariableWord_symbol
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n) :
    (fibreQVariableWord c fallback w).word s =
      fibreQSymbol c fallback w s :=
  rfl

/-- The actual FULL-fibre corrected Q is now packaged as a
legal starred variable word on the exact corrected projected
D0/D2 Q support, not a substitute old-word placeholder. -/
noncomputable def fibreQStarredWord
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) := {
  tree := (nodes c.core
    (ForwardQEnlargedConstantWords.eraseAux
      c.core fallback w.1)).toList
  tree_bounded :=
    ForwardQRetainedWordScaffold.Q_nodes_bounded_of_ambient_bound
      c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1)
      c.T_bounded
  semi_complete :=
    ForwardQActualStarredSpace.actual_starred_Q_semiComplete
      hb c.core
      (ForwardQEnlargedConstantWords.toStarredInput
        c.core fallback w)
  word := fibreQVariableWord c fallback w.1
  interior_card :=
    ForwardQRetainedWordScaffold.Q_interior_card_eq_source_dimension
      hb c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1)
  support_eq_interior := fun s =>
    ForwardQRetainedWordScaffold.original_word_support_iff_Q_interior
      hb c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1) s
  support_skew := c.core.source.support_skew
}

theorem fibreQStarredWord_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    (fibreQStarredWord hb c fallback w).tree =
      (nodes c.core
        (ForwardQEnlargedConstantWords.eraseAux
          c.core fallback w.1)).toList :=
  rfl

theorem fibreQStarredWord_symbol
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (s : BoundedNode b n) :
    (fibreQStarredWord hb c fallback w).word.word s =
      fibreQSymbol c fallback w.1 s :=
  rfl

/-- Correctness of the starred variable-support roots as
ACTUAL Q interior nodes, not just equality of cardinalities. -/
theorem fibreQStarredWord_support_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (t : Node b) :
    t ∈ (fibreQStarredWord hb c fallback w).word.supportNodes ↔
      t ∈ SkewTree.interior
        (fibreQStarredWord hb c fallback w).tree :=
  (fibreQStarredWord hb c fallback w).support_eq_interior t

/-- Printed Lemma 27(iv) now holds in a GENUINE finished
starred word at EVERY ambient position in the full original
f fibre of P_i(z), for both enlarged alphabet constructors. -/
theorem fibreQStarredWord_projected_full_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (i : ForwardQAmbientFibreSymbol.Index c)
    (z : BoundedNode b (k - (m + 1)))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).2)) :
    (fibreQStarredWord hb c fallback w).word.word s =
      match w.1.words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j := by
  change fibreQSymbol c fallback w.1 s = _
  exact fibreQ_projected_full_fibre c fallback w.1 i z s hs

/-- Old source roots, and specifically the retained cut,
stay fixed in the finalized starred Q word. -/
theorem fibreQStarredWord_at_old_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (v : c.core.source.word.Vars) :
    (fibreQStarredWord hb c fallback w).word.word v.1 =
      Sum.inr v := by
  change fibreQSymbol c fallback w.1 v.1 = Sum.inr v
  exact fibreQ_at_old_root c fallback w.1 v

end DualTree.ForwardQAmbientFibreLegalWord
