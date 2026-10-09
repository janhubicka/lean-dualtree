import DualTree.SkewTree

/-!
# A finite obstruction to arbitrary-depth Q marker replacement

This checks the exact Boolean skew clauses, not an informal surrogate.
Take the complete binary skew support through intrinsic height two,
with a source star having only the root as interior.  If the two
terminal signature markers are independently replaced by an extension
of the left child and by the right child itself, the resulting
three-node support is rooted and has exactly two immediate branches,
but *fails* the source's skew clause (ii): the lexicographically
earlier terminal node at intrinsic height one is longer.

The finite tests below are kernel-checked.  This module does not
claim yet that this precise selection is realized by the actual
typed mixed-product Q map; that source-facing instantiation is a
separate verification obligation. It does prove the necessary
warning: prefix geometry and exact b-fold branching do not imply
the source's order-length conditions.
-/

namespace DualTree.QLengthObstruction

/-- The 3-complete homogeneous binary skew support. -/
def completeT : List (Node 2) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

/-- A 2-semi-complete starred source support with a single
interior root and two literal terminal markers. -/
def originalS : List (Node 2) := [[], [0], [1]]

/-- Replace the left leaf by a deeper node, retain the right leaf. -/
def extendedLeft : List (Node 2) := [[], [0, 0], [1]]

theorem completeT_is_complete :
    SkewTree.completeB SkewTree.paperAuxB 3 completeT = true := by
  decide

theorem originalS_is_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB originalS = true := by
  decide

theorem extendedLeft_rooted :
    SkewTree.rootedB extendedLeft = true := by
  decide

theorem extendedLeft_exact_branching :
    (SkewTree.immediateSuccs extendedLeft ([] : Node 2)).length = 2 := by
  decide

theorem extendedLeft_condIIB_fails :
    SkewTree.condIIB extendedLeft = false := by
  decide

theorem extendedLeft_condIIIB_holds :
    SkewTree.condIIIB extendedLeft = true := by
  decide

theorem extendedLeft_lastWitness_holds :
    SkewTree.condIVB SkewTree.paperAuxB extendedLeft = true := by
  decide

theorem extendedLeft_not_skew :
    SkewTree.skewB SkewTree.paperAuxB extendedLeft = false := by
  decide

theorem extendedLeft_not_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB extendedLeft = false := by
  decide

end DualTree.QLengthObstruction
