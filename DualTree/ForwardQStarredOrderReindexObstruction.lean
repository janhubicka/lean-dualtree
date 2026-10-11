import DualTree.QLengthStarredCoordinateOrder
import DualTree.ForwardQActualStarredSpace

/-!
# Non-invariance of starred D₂ point order under the forward-order repair

The printed Lemma 27 orders the frontier coordinates by
length-first *reverse* lexicographic order. The consistent
geometric repair instead sorts equal-length frontiers in
*forward* lexicographic order.

In the typed binary height-three counterexample, the two
selected frontiers are the right child [1] and the left
child [0] of the empty cut. The paper orders them (right,left),
while the corrected forward order is (left,right).
The same marker-to-point assignment attaches the empty
local tail to right and the length-one tail [0] to left.

In the printed order the singleton D₂ length vector is
(0,1) and is vector-1-complete. In the corrected order,
*without reassigning local tails*, it becomes (1,0)
and fails the same exact executable vector-1-complete test.

Thus a naive switch to the forward auxiliary order does
not automatically transport every original starred input
to the corrected W-star subtype. The colourings, marker
indexing, local cone words and recursive Ramsey parameters
must be transported/reorganized together, or the repaired
statement must explicitly restrict the source domain.
This counterexample concerns naive reindexing of inputs;
it does not refute the conditional geometric forward-Q
theorem or the final dual Ramsey conclusion.
-/

namespace DualTree.ForwardQStarredOrderReindexObstruction

/-- The printed reverse-lex order puts the right child first. -/
theorem printed_right_before_left :
    PaperAux ([1] : Node 2) ([0] : Node 2) :=
  QLengthStarredDomain.right_before_left

/-- The corrected forward-lex order reverses this pair
of equal-length frontier children. -/
theorem corrected_left_before_right :
    ForwardAux ([0] : Node 2) ([1] : Node 2) := by
  decide

/-- Preserve the ACTUAL typed marker-to-local-point assignment
from the original witness, but enumerate its marked singleton
supports in corrected (left,right) order. -/
noncomputable def correctedOrderActualMarkedSingletonSupports
    (i : Fin 2) : List (Node 2) :=
  if i.val = 0 then
    [(QLengthTypedWitness.mixed.bulletPoint
      (QLengthProjected.index QLengthTypedWitness.leftMarker)).1]
  else
    [(QLengthTypedWitness.mixed.bulletPoint
      (QLengthProjected.index QLengthTypedWitness.rightMarker)).1]

/-- The corrected enumeration turns the actual local-tail list
into the (length-one,empty) singleton vector, not an
arbitrarily selected alternative tuple. -/
theorem corrected_order_actual_eq_reversed :
    correctedOrderActualMarkedSingletonSupports =
      QLengthStarredDomain.reversedMarkedSingletonSupports := by
  have hRight :
      (QLengthTypedWitness.mixed.bulletPoint
        (QLengthProjected.index QLengthTypedWitness.rightMarker)).1 =
          ([] : Node 2) := by
    simpa [QLengthProjected.index, QLengthTypedWitness.chosenPoint,
      QLengthTypedWitness.rightMarker] using
      (congrArg Subtype.val QLengthTypedWitness.right_bullet_is_chosen)
  have hLeft :
      (QLengthTypedWitness.mixed.bulletPoint
        (QLengthProjected.index QLengthTypedWitness.leftMarker)).1 =
          ([0] : Node 2) := by
    simpa [QLengthProjected.index, QLengthTypedWitness.chosenPoint,
      QLengthTypedWitness.leftMarker] using
      (congrArg Subtype.val QLengthTypedWitness.left_bullet_is_chosen)
  funext i
  by_cases hi : i.val = 0
  · simp [correctedOrderActualMarkedSingletonSupports,
      QLengthStarredDomain.reversedMarkedSingletonSupports, hi, hLeft]
  · simp [correctedOrderActualMarkedSingletonSupports,
      QLengthStarredDomain.reversedMarkedSingletonSupports, hi, hRight]

/-- The ACTUAL printed-order tuple passes the source's starred
vector-1-complete test. -/
theorem printed_actual_is_starred :
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
      QLengthStarredDomain.actualMarkedSingletonSupports = true :=
  QLengthStarredDomain.actual_marked_points_in_starred_domain

/-- Keeping the same actual marker-to-local-point assignment
and simply enumerating it in corrected forward order FAILS
the vector-1-complete starred condition. -/
theorem corrected_fixed_assignment_not_starred :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      correctedOrderActualMarkedSingletonSupports = false := by
  rw [corrected_order_actual_eq_reversed]
  decide

/-- Fully source-facing non-transport certificate for the
two ordered actual marker families, with no unsupported
claim about large-parameter instances of the full theorem. -/
theorem naive_reindexing_breaks_starred_domain :
    PaperAux ([1] : Node 2) ([0] : Node 2) ∧
    ForwardAux ([0] : Node 2) ([1] : Node 2) ∧
    VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
      QLengthStarredDomain.actualMarkedSingletonSupports = true ∧
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      correctedOrderActualMarkedSingletonSupports = false :=
  ⟨printed_right_before_left, corrected_left_before_right,
   printed_actual_is_starred, corrected_fixed_assignment_not_starred⟩

end DualTree.ForwardQStarredOrderReindexObstruction
