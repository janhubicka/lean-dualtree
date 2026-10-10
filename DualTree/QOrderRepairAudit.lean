import DualTree.QLengthStarredCoordinateOrder
import DualTree.VectorSkew

/-!
# Two distinct proposed repairs of the Lemma 27 Q order obstruction

The literal counterexample to Q uses length-first *reverse* lexicographic
auxiliary order. Reordering the D₂ frontier coordinates in forward
lexicographic order fixes the two-leaf root example, but this change
alone does not fix Q for all semi-complete source supports.

A deeper source support of height three has an interior node at [1].
Independently assigning the one-letter local tail [0] to every
new marker (which is vector 1-complete in **any** coordinate order)
replaces the leaf [0] by [0,0], while retaining the interior [1].
These have equal Q-intrinsic height, but reversed ambient lengths.
Thus **reordering only the frontier coordinates cannot be the
full correction** to Lemma 27.

When the *global auxiliary order* is instead changed to forward
lexicographic on ties, this original source is no longer skew,
and its mirror image [[],[0],[1],[0,0],[0,1]] is skew. The
corresponding replacement example passes the full semi-complete
skew check. These are exact kernel regression tests, not a
general proof that the global forward-order convention repairs
all parts of the published argument.
-/

namespace DualTree.QOrderRepairAudit

/-- Repaired root-cut output when lexically earlier frontier 0
receives the shorter local tail. -/
def rootForwardIndexedQ : List (Node 2) :=
  [[], [0], [1, 0]]

theorem root_forward_indexed_Q_is_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB
      rootForwardIndexedQ = true := by
  decide

/-- A nonsymmetric source, semi-complete under the
original reverse-lex auxiliary order, with two interior
vertices [] and [1]. -/
def deepPrintedSource : List (Node 2) :=
  [[], [0], [1], [1, 0], [1, 1]]

theorem deep_printed_source_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB
      deepPrintedSource = true := by
  decide

/-- This source *does not* satisfy the globally modified
forward auxiliary order, so merely switching the order
changes the source class rather than preserving this example. -/
theorem deep_printed_source_not_forward_semiComplete :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      deepPrintedSource = false := by
  decide

/-- This is the actual Q-like tree obtained at cut [1] in the
full binary support of height four by using a one-letter
tail [0] at each of the three marked coordinates. The
order of the three frontiers is immaterial to this choice. -/
def deepReindexOnlyQ : List (Node 2) :=
  [[], [1], [0, 0], [1, 0, 0], [1, 1, 0]]

/-- The source-side auxiliary order can be reversed or its
frontier list reindexed, but the Q tree still violates the
independent skew condition (ii). -/
theorem deep_reindex_only_Q_fails_condII :
    SkewTree.condIIB deepReindexOnlyQ = false := by
  decide

theorem deep_reindex_only_Q_not_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB
      deepReindexOnlyQ = false := by
  decide

/-- All three local marked nodes are the same word [0].
Their vector 1-completeness is unchanged by reordering. -/
def equalLengthMarkedPoints (_ : Fin 3) : List (Node 2) := [[0]]

theorem equal_length_marked_points_are_vector_one_complete :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
      equalLengthMarkedPoints = true := by
  decide

/-- The mirror image of the deeper source is semi-complete
under the globally *forward*-lex auxiliary order. -/
def deepForwardSource : List (Node 2) :=
  [[], [0], [1], [0, 0], [0, 1]]

theorem deep_forward_source_semiComplete :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      deepForwardSource = true := by
  decide

/-- In the same full binary support, the analogous Q leaf
replacement is compatible with all forward-order skew axioms. -/
def deepForwardQ : List (Node 2) :=
  [[], [0], [1, 0], [0, 0, 0], [0, 1, 0]]

theorem deep_forward_Q_semiComplete :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      deepForwardQ = true := by
  decide

end DualTree.QOrderRepairAudit
