import DualTree.QLengthStarredDomain

/-!
# Checking actual D₂ coordinate positions, not just paper order abstractly

In the author's construction, the distinguished two literal markers
receive coordinates in the list of minimal support frontiers, ordered
by the printed auxiliary order. The preceding module verified that
the concrete frontier list is (right,left) and that the resulting
marked-point tuple (empty,0) is vector 1-complete.

Here we connect the *noncomputable actual coordinate map* directly
to its list positions, proving that the right marker has coordinate
zero and the left marker has coordinate one. Together these lemmas
close the missing index/Definition-20 starred-domain check for
the small-height Q counterexample.
-/

namespace DualTree.QLengthStarredCoordinateOrder

open QLengthTypedWitness

private noncomputable def F : List (Node 2) :=
  LiteralFrontierCount.frontiers QLengthObstruction.completeT
    ([] : Node 2)

private abbrev Marker := QLengthProjected.Marker

private noncomputable def idx (s : Marker) : Fin F.length :=
  LiteralMarkerCoordinates.coordinate
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early s

/-- Actual marker-coordinate choice is identified by the
element retrieved from the duplicate-free frontier enumeration. -/
private theorem idx_eq_of_frontier_get (s : Marker)
    (t : Node 2)
    (hfr : LiteralFrontierIndex.frontierFor
      source [] root_interior root_maximal exceptional_outside
      QLengthObstruction.completeT
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early s = t)
    (j : Fin F.length)
    (hj : F.get j = t) :
    idx s = j := by
  have hChosen : F.get (idx s) = t := by
    calc
      F.get (idx s) =
          LiteralFrontierIndex.frontierFor
            source [] root_interior root_maximal exceptional_outside
            QLengthObstruction.completeT
            QLengthObstruction.completeT_is_complete
            source_subset_complete cut_in_complete cut_level_early s :=
        LiteralMarkerCoordinates.coordinate_frontier
          source [] root_interior root_maximal exceptional_outside
          QLengthObstruction.completeT
          QLengthObstruction.completeT_is_complete
          source_subset_complete cut_in_complete cut_level_early s
      _ = t := hfr
  let e := List.Nodup.getEquiv F
    (LiteralFrontierCount.frontiers_nodup
      QLengthObstruction.completeT ([] : Node 2))
  have heq : e (idx s) = e j := by
    apply Subtype.ext
    exact hChosen.trans hj.symm
  exact e.injective heq

/-- The index of the right literal marker is the first
coordinate, precisely as required by the printed auxiliary order. -/
theorem right_index_is_zero :
    (idx rightMarker).val = 0 := by
  let j : Fin F.length := ⟨0, by
    simp [F, QLengthStarredDomain.actual_frontier_order]⟩
  have hj : F.get j = ([1] : Node 2) := by
    simp [F, QLengthStarredDomain.actual_frontier_order, j]
  have h := idx_eq_of_frontier_get rightMarker ([1] : Node 2)
    QLengthProjected.right_frontier_eq j hj
  exact congrArg Fin.val h

/-- The index of the left literal marker is the second
coordinate in the paper's right/left frontier enumeration. -/
theorem left_index_is_one :
    (idx leftMarker).val = 1 := by
  let j : Fin F.length := ⟨1, by
    simp [F, QLengthStarredDomain.actual_frontier_order]⟩
  have hj : F.get j = ([0] : Node 2) := by
    simp [F, QLengthStarredDomain.actual_frontier_order, j]
  have h := idx_eq_of_frontier_get leftMarker ([0] : Node 2)
    QLengthProjected.left_frontier_eq j hj
  exact congrArg Fin.val h

/-- The actual coordinate map orders the two bullet points
(right,left), and their selected local heights increase (0,1),
so the true source W_* requirement is met. -/
theorem actual_starred_input_certificate :
    (idx rightMarker).val < (idx leftMarker).val ∧
      VectorSkew.vectorCompleteB SkewTree.paperAuxB 1
        QLengthStarredDomain.actualMarkedSingletonSupports = true := by
  constructor
  · rw [right_index_is_zero, left_index_is_one]
    omega
  · exact QLengthStarredDomain.actual_marked_points_in_starred_domain

end DualTree.QLengthStarredCoordinateOrder
