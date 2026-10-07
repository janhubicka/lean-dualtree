import DualTree.SkewTree

/-!
# Vector complete skew trees

Section 3.2 packages several complete skew trees into a vector tree.  Besides
componentwise completeness, nodes at the same intrinsic level are ordered by
their ambient lengths across coordinates, and consecutive intrinsic levels are
strictly separated in ambient length.

This file gives a finite executable version of the vector-complete notion.  As
elsewhere in the validation, the auxiliary node order is an explicit
parameter, so both the printed and repaired conventions can be tested against
the same definition.
-/

namespace DualTree.VectorSkew

open SkewTree

/-- Nodes of intrinsic level m in a finite skew-tree component. -/
def levelNodes {b : Nat} (S : List (Node b)) (m : Nat) : List (Node b) :=
  S.filter (fun s => decide (heightAt S s = m))

/-- Condition (ii) of the vector-skew definition. -/
def sameLevelOrderedB {b d : Nat}
    (S : Fin d → List (Node b)) (k : Nat) : Bool :=
  (allFin d).all (fun i =>
    (allFin d).all (fun j =>
      if i < j then
        (List.range k).all (fun m =>
          (levelNodes (S i) m).all (fun s =>
            (levelNodes (S j) m).all (fun t =>
              decide (s.length ≤ t.length))))
      else
        true))

/-- Condition (iii) of the vector-skew definition. -/
def successiveLevelsSeparatedB {b d : Nat}
    (S : Fin d → List (Node b)) (k : Nat) : Bool :=
  (List.range (k - 1)).all (fun m =>
    (allFin d).all (fun i =>
      (allFin d).all (fun j =>
        (levelNodes (S i) m).all (fun s =>
          (levelNodes (S j) (m + 1)).all (fun t =>
            decide (s.length < t.length))))))

/--
Vector k-complete skew tree: each component is k-complete and the cross-
coordinate level-ordering clauses hold.
-/
def vectorCompleteB {b d : Nat}
    (aux : Node b → Node b → Bool)
    (k : Nat) (S : Fin d → List (Node b)) : Bool :=
  (allFin d).all (fun i => completeB aux k (S i)) &&
    sameLevelOrderedB S k &&
    successiveLevelsSeparatedB S k

def VectorComplete {b d : Nat}
    (aux : Node b → Node b → Bool)
    (k : Nat) (S : Fin d → List (Node b)) : Prop :=
  vectorCompleteB aux k S = true

/-- Small nontrivial two-coordinate height-one example. -/
def binaryHeightOneVector : Fin 2 → List (Node 2)
  | ⟨0, _⟩ => [[]]
  | ⟨1, _⟩ => [[(0 : Fin 2)]]

/-- The coordinates are in the ambient-length order required by clause (ii). -/
theorem binaryHeightOneVector_complete :
    vectorCompleteB forwardAuxB 1 binaryHeightOneVector = true := by
  decide

/-- Reversing those two coordinates violates the same-level ordering clause. -/
def binaryHeightOneVectorReversed : Fin 2 → List (Node 2)
  | ⟨0, _⟩ => [[(0 : Fin 2)]]
  | ⟨1, _⟩ => [[]]

theorem binaryHeightOneVectorReversed_not_complete :
    vectorCompleteB forwardAuxB 1 binaryHeightOneVectorReversed = false := by
  decide

end DualTree.VectorSkew
