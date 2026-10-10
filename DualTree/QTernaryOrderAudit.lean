import DualTree.QOrderRepairAudit

/-!
# Ternary finite regression for the proposed global forward order

For the complete ternary support 3^{<3} and the root-cut
starred source, the printed reverse-lex frontier enumeration
is (2,1,0). Taking D₂ singleton marked points (empty,empty,0)
in that order is vector 1-complete, but yields Q tree
{empty,0·0,1,2}, which is not skew.

With the forward-lex order adopted *consistently*, the
frontier sequence is (0,1,2), and the same marked-point tuple
yields {empty,0,1,2·0}, which is semi-complete skew.

These tests cover concrete finite support shapes, not the
fully typed arbitrary-height Q map. An independent Python
regression exhaustively checks all 1600 admissible ternary
root-cut Q cases at complete height three.
-/

namespace DualTree.QTernaryOrderAudit

def source : List (Node 3) := [[], [0], [1], [2]]

theorem source_is_printed_semiComplete :
    SkewTree.semiCompleteB SkewTree.paperAuxB source = true := by
  decide

theorem source_is_forward_semiComplete :
    SkewTree.semiCompleteB SkewTree.forwardAuxB source = true := by
  decide

/-- The actual vector 1-complete ordered tuple
(empty,empty,0), admissible for both coordinate
enumerations when using a common three-coordinate type. -/
def marked (i : Fin 3) : List (Node 3) :=
  if i.val = 2 then [[0]] else [[]]

theorem marked_is_vector_one_complete :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1 marked = true := by
  decide

def printedQ : List (Node 3) := [[], [0, 0], [1], [2]]

theorem printed_Q_fails_condII :
    SkewTree.condIIB printedQ = false := by
  decide

def globallyForwardQ : List (Node 3) := [[], [0], [1], [2, 0]]

theorem globally_forward_Q_is_semiComplete :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      globallyForwardQ = true := by
  decide

end DualTree.QTernaryOrderAudit
