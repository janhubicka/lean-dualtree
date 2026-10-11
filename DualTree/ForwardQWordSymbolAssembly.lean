import DualTree.ForwardQRetainedWordScaffold
import DualTree.ForwardQCertifiedSemiComplete

/-!
# A source-facing assembly interface for the genuine corrected Q word

The corrected Q support is known to preserve exactly the old source
interior as its set of variable roots, and to be semi-complete skew
under the selected D₂ point-order hypothesis. Constructing the
particular mixed-cone output word g_w of Lemma 27 remains open.

The interface here separates the purely structural typing task:
given a total decoded symbol map on the original homogeneous tree
whose variables are *exactly the old source roots*, prove
  (a) at every variable root, the symbol is its own variable;
  (b) whenever variable v occurs, the root of v is an ambient
      prefix of its occurrence.

The two conditions suffice to package the decoded map as a legal
tree-variable word. Since the source root set is exactly the
reconstructed Q interior, the same map then yields a genuine
StarredWord on the ACTUAL corrected Q support, given the existing
explicit ambient T boundedness assumption.

This is not the construction of a particular decoded map and does
not assert that every cone patch satisfies the two conditions.
It is the final structural assembly lemma to be invoked once
the individual cone maps, root-aligned source substitution and
auxiliary decoding are connected. Smoothness/colouring remains
a separate obligation.
-/

namespace DualTree.ForwardQWordSymbolAssembly

open ForwardSourceQTree

/-- The exact two conditions on a candidate Q output word
after all its original/auxiliary/cone-variable symbols
have been translated into constants or *source-root*
variable names. -/
structure DecodedWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) where
  symbol : BoundedNode b n → Sum α c.source.word.Vars
  atRoot : ∀ v : c.source.word.Vars, symbol v.1 = Sum.inr v
  below : ∀ v : c.source.word.Vars,
    ∀ i : BoundedNode b n,
      symbol i = Sum.inr v → IsPrefix v.1.1 i.1

/-- Every total decoded symbol map satisfying the two root
axioms is a legal tree-variable word with precisely the
original source variable-root support. -/
def DecodedWord.toVariableWord
    {b n l k m : Nat} {α : Type*}
    {c : Frame b n l k m α}
    (g : DecodedWord c) :
    DualTree.VariableWord b n α where
  support := c.source.word.support
  support_nodup := c.source.word.support_nodup
  word := g.symbol
  atRoot := g.atRoot
  below := g.below

/-- The symbol of the assembled word is exactly the specified
candidate decoded symbol at every ambient coordinate. -/
theorem toVariableWord_symbol
    {b n l k m : Nat} {α : Type*}
    {c : Frame b n l k m α}
    (g : DecodedWord c)
    (i : BoundedNode b n) :
    g.toVariableWord.word i = g.symbol i := rfl

/-- The decoded word retains the original source variable roots
as an exact list, not just up to a permutation or refinement. -/
theorem toVariableWord_support
    {b n l k m : Nat} {α : Type*}
    {c : Frame b n l k m α}
    (g : DecodedWord c) :
    g.toVariableWord.support = c.source.word.support := rfl

/-- The actual corrected Q support and a legal decoded word
assemble into a valid starred object. The input Q must satisfy
the selected D₂ length order; this is a certified geometric
premise, not an assertion about unstarred mixed-product points. -/
noncomputable def DecodedWord.onCorrectedQ
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (g : DecodedWord c) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) where
  tree := (nodes c x).toList
  tree_bounded :=
    ForwardQRetainedWordScaffold.Q_nodes_bounded_of_ambient_bound
      c x hTbound
  semi_complete :=
    ForwardQCertifiedSemiComplete.Q_semiComplete_of_bullet_lengths
      hb c x hordered
  word := g.toVariableWord
  interior_card :=
    ForwardQRetainedWordScaffold.Q_interior_card_eq_source_dimension
      hb c x
  support_eq_interior := by
    intro t
    change t ∈ c.source.word.supportNodes ↔
      t ∈ SkewTree.interior (nodes c x).toList
    exact ForwardQRetainedWordScaffold.original_word_support_iff_Q_interior
      hb c x t
  support_skew := by
    intro hl
    change SkewTree.skewB SkewTree.forwardAuxB
      c.source.word.supportNodes = true
    exact c.source.support_skew hl

/-- The constructed starred object has exactly the Q support,
not the enlarged ambient complete T support. -/
theorem onCorrectedQ_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (g : DecodedWord c) :
    (g.onCorrectedQ hb c x hordered hTbound).tree =
      (nodes c x).toList := rfl

/-- No decoded symbol is modified by the final packaging step:
the variable-word component is precisely the original candidate
function at each ambient coordinate. -/
theorem onCorrectedQ_symbol
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (g : DecodedWord c)
    (i : BoundedNode b n) :
    (g.onCorrectedQ hb c x hordered hTbound).word.word i =
      g.symbol i := rfl

/-- There is at least one well-typed decoded-word candidate:
the old source word. It is only a placeholder; no mixed-cone
colouring or Lemma 27 output is claimed for this choice. -/
def sourcePlaceholder
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    DecodedWord c where
  symbol := c.source.word.word
  atRoot := c.source.word.atRoot
  below := c.source.word.below

end DualTree.ForwardQWordSymbolAssembly
