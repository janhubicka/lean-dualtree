import DualTree.QLengthActualSkewFailure
import DualTree.VectorSkew

/-!
# The missing starred-domain and frontier-order check

Definition 20 of the Todorcevic--Tyros paper does not define W^D_* as
the whole mixed product W^D. At the marked D₂ coordinates, the tuple
must be a vector 1-complete skew subtree. In the binary witness
that means the selected local point lengths must be nondecreasing
in the enumerated D₂-coordinate order.

The paper enumerates frontier nodes by its length-first, reverse-lex
auxiliary order; at the root cut the correct order is (1,0), not
(0,1). The chosen local points at these coordinates are respectively
the empty word and 0, of lengths (0,1), satisfying the vector
1-completeness condition.

This module explicitly checks the vector complete predicate and
the strict order of the two literal frontier markers. The
source-facing auxiliary-frontier enumeration will be tracked
separately if its noncomputable list needs a dedicated normalization
lemma. We must not mistake ordinary mixed-product membership for
starred-domain membership.
-/

namespace DualTree.QLengthStarredDomain

/-- Actual source auxiliary-order orientation among the two
children of the root cut: the right child precedes the left. -/
theorem right_before_left :
    PaperAux ([1] : Node 2) ([0] : Node 2) := by
  decide

theorem left_not_before_right :
    ¬ PaperAux ([0] : Node 2) ([1] : Node 2) := by
  decide

/-- The coordinate order prescribed by the paper is right,
then left, and the corresponding local D₂ points are empty,
then 0. Each singleton itself forms a 1-complete skew tree. -/
def markedSingletonSupports : Fin 2 → List (Node 2)
  | ⟨0, _⟩ => [[]]
  | ⟨1, _⟩ => [[0]]
  | _ => []

/-- This is the exact starred-domain vector 1-completeness check:
the marked tuple (empty,0), in the order (right,left), is
admissible in Definition 20. -/
theorem marked_points_vector_one_complete :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
      markedSingletonSupports = true := by
  decide

/-- Reversing the coordinate order of these two marked points
does *not* satisfy the starred-domain ordering axiom. -/
def reversedMarkedSingletonSupports : Fin 2 → List (Node 2)
  | ⟨0, _⟩ => [[0]]
  | ⟨1, _⟩ => [[]]
  | _ => []

theorem reversed_points_not_vector_one_complete :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
      reversedMarkedSingletonSupports = false := by
  decide

/-- The actual finite support list is placed in the
length-first reverse-lex order chosen in the printed proof. -/
theorem completeT_right_before_left :
    ([1] : Node 2) ∈ QLengthObstruction.completeT ∧
    ([0] : Node 2) ∈ QLengthObstruction.completeT ∧
    PaperAux ([1] : Node 2) ([0] : Node 2) := by
  simp [QLengthObstruction.completeT, right_before_left]

/-- The explicitly selected frontier nodes are the right and
left children, so the printed enumeration is (right,left). -/
theorem actual_frontier_order :
    LiteralFrontierCount.frontiers QLengthObstruction.completeT
      ([] : Node 2) =
      ([([1] : Node 2), ([0] : Node 2)] : List (Node 2)) := by
  classical
  simp [LiteralFrontierCount.frontiers, QLengthObstruction.completeT,
    CutFrontier.Frontier, PaperAux, FinLexLE, finLexLEB,
    IsStrictPrefix, IsPrefix]

end DualTree.QLengthStarredDomain
