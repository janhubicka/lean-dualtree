import DualTree.VectorSkew
import DualTree.DirectionalSupport

/-!
# Exact length monotonicity from the starred D₂ vector-1-complete test

Definition 20 of the paper restricts the D₂ marked coordinates
to a vector 1-complete skew subtree. The coordinates are ordered.
Every component at height one is a singleton marked node.

The vector-complete condition imposes that, for all coordinate
indices i<j, the chosen singleton points satisfy

      |s_i| ≤ |s_j|.

This file derives that inequality directly from the executable
VectorSkew.sameLevelOrderedB / vectorCompleteB definitions for
arbitrary branching number b and number of coordinates d.

This closes a subtle proof-interface gap: the repaired Q map
cannot assume an arbitrary nondecreasing-length hypothesis
without linking it to the actual W_* domain restriction. The
result is purely about mixed-product marked point order, not
about Q semi-completeness or its colouring.
-/

namespace DualTree.VectorOneMarkedLengths

/-- Any singleton support node has intrinsic rank zero in
its one-node support, so it belongs to level zero. -/
theorem singleton_at_zero {b : Nat} (s : Node b) :
    s ∈ VectorSkew.levelNodes [s] 0 := by
  change s ∈ ([s].filter
    (fun u => decide (SkewTree.heightAt [s] u = 0)))
  apply List.mem_filter.mpr
  constructor
  · simp
  · simp [SkewTree.heightAt, SkewTree.preds, SkewTree.strictPrefixB]

/-- The exact same-level vector skew condition at intrinsic
height 1 forces nondecreasing ambient lengths for the
singleton marked point at every ordered pair of indices. -/
theorem lengths_mono_of_sameLevelOrdered
    {b d : Nat}
    (point : Fin d → Node b)
    (hlevel : VectorSkew.sameLevelOrderedB
        (fun i => [point i]) 1 = true)
    (i j : Fin d) (hij : i < j) :
    (point i).length ≤ (point j).length := by
  unfold VectorSkew.sameLevelOrderedB at hlevel
  have hi := (List.all_eq_true.mp hlevel)
    i (DirectionalSupport.mem_allFin d i)
  have hj := (List.all_eq_true.mp hi)
    j (DirectionalSupport.mem_allFin d j)
  have hlevels :
      (List.range 1).all
        (fun m =>
          (VectorSkew.levelNodes [point i] m).all
            (fun s =>
              (VectorSkew.levelNodes [point j] m).all
                (fun t => decide (s.length ≤ t.length)))) = true := by
    simpa [hij] using hj
  have hzero := (List.all_eq_true.mp hlevels) 0 (by simp)
  have hleft := (List.all_eq_true.mp hzero)
    (point i) (singleton_at_zero (point i))
  have hright := (List.all_eq_true.mp hleft)
    (point j) (singleton_at_zero (point j))
  simpa using hright

/-- Source-facing Definition 20: vector 1-completeness of
the ordered singleton D₂ coordinates implies precisely
the local point-length monotonicity used by the corrected
forward Q projection. The auxiliary order can be arbitrary
since every individual component is a singleton. -/
theorem lengths_mono_of_vectorOneComplete
    {b d : Nat}
    (aux : Node b → Node b → Bool)
    (point : Fin d → Node b)
    (hvector : VectorSkew.vectorCompleteB aux 1
      (fun i => [point i]) = true)
    (i j : Fin d) (hij : i < j) :
    (point i).length ≤ (point j).length := by
  have hs : VectorSkew.sameLevelOrderedB
      (fun i => [point i]) 1 = true := by
    have hh := hvector
    simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true] at hh
    exact hh.1.2
  exact lengths_mono_of_sameLevelOrdered point hs i j hij

end DualTree.VectorOneMarkedLengths
