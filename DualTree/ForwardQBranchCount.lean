import DualTree.ForwardQAllDirections
import DualTree.Lemma27QBranchCount

/-!
# Exact numerical branching in the genuine forward-corrected Q support

The meet-closed Q support has at most one immediate successor in
each ambient direction. The previous source-facing directional
occupancy theorem supplies an actual descendant in every direction
from every old source interior vertex. Using the already checked
immediate-branch extraction lemma, each such cone contains exactly
one immediate Q support successor.

Since the Q interior equals the original interior, every Q vertex
is either terminal or has exactly b immediate Q successors. The
Boolean branching component of semiCompleteB is therefore always
satisfied (for b>0), and full semi-completeness reduces precisely
to the independent skewB predicate.

This does not assert skew clauses (ii)/(iii), the final branching
witness, or the original word/colouring part.
-/

namespace DualTree.ForwardQBranchCount

open ForwardSourceQTree

/-- Each actual Q nonleaf occupies every ambient branch in
exactly one immediate support successor. -/
theorem Q_full_immediate_at_nonleaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior (nodes c x).toList)
    (i : Fin b) :
    SkewTree.uniqueBranchB (nodes c x).toList s i = true := by
  have hsOld : s ∈ SkewTree.interior c.source.tree :=
    (ForwardQInteriorExact.Q_interior_iff_original
      hb c x s).1 hs
  exact ForwardQAllDirections.Q_full_immediate_directions
    c x s hsOld i

/-- Every actual corrected Q vertex has either zero or exactly
b immediate successors, without asserting the remaining
skew rank/ambient-length conditions. -/
theorem Q_zero_or_b
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ (nodes c x).toList) :
    (SkewTree.immediateSuccs (nodes c x).toList s).length = 0 ∨
    (SkewTree.immediateSuccs (nodes c x).toList s).length = b := by
  let W := nodes c x
  by_cases hzero : (SkewTree.immediateSuccs W.toList s).length = 0
  · exact Or.inl hzero
  · right
    have hsInterior : s ∈ SkewTree.interior W.toList := by
      unfold SkewTree.interior
      apply List.mem_filter.mpr
      refine ⟨hs, ?_⟩
      cases heq : SkewTree.immediateSuccs W.toList s with
      | nil =>
          simp [heq] at hzero
      | cons u us =>
          simp [heq]
    exact Lemma27QBranchCount.immediateSuccs_length_eq_of_full_directions
      W.toList (Finset.nodup_toList W) s
      (fun i => Q_full_immediate_at_nonleaf hb c x s hsInterior i)

/-- The literal Boolean branching conjunct in semiCompleteB,
evaluated on the true corrected Q support, is discharged. -/
theorem Q_boolean_branch_clause
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    (nodes c x).toList.all (fun s =>
      decide ((SkewTree.immediateSuccs
        (nodes c x).toList s).length = 0 ∨
        (SkewTree.immediateSuccs
          (nodes c x).toList s).length = b)) = true := by
  let W := nodes c x
  change W.toList.all
    (fun s => decide
      ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
       (SkewTree.immediateSuccs W.toList s).length = b)) = true
  apply List.all_eq_true.mpr
  intro s hs
  simpa only [decide_eq_true_eq] using Q_zero_or_b hb c x s hs

/-- The actual corrected Q support is semi-complete skew exactly
when its independent skewB predicate holds. In particular no
numerical branching argument remains to be proved. -/
theorem Q_semiComplete_iff_skew
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true ↔
    SkewTree.skewB SkewTree.forwardAuxB
      (nodes c x).toList = true := by
  let W := nodes c x
  have hbranch : W.toList.all
      (fun s => decide
        ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
         (SkewTree.immediateSuccs W.toList s).length = b)) = true :=
    Q_boolean_branch_clause hb c x
  change (SkewTree.skewB SkewTree.forwardAuxB W.toList &&
    W.toList.all (fun s =>
      let d := (SkewTree.immediateSuccs W.toList s).length
      decide (d = 0 ∨ d = b))) = true ↔
    SkewTree.skewB SkewTree.forwardAuxB W.toList = true
  simp only [Bool.and_eq_true]
  constructor
  · exact And.left
  · intro hskew
    exact ⟨hskew, hbranch⟩

end DualTree.ForwardQBranchCount
