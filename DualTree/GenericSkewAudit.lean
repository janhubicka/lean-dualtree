import DualTree.SkewTree

/-!
# Generic Section 3 counterexamples

The first audit used a binary Bool executable checker.  This file repeats the
two important finite counterexamples directly in the generic `SkewTree`
definitions used by the formal development.

Thus no separate checker-equivalence lemma is needed to conclude that the
printed Remark 2 is false, or that the extension clause of Remark 1 remains
false after the natural forward-lex repair.
-/

namespace DualTree.GenericSkewAudit

open SkewTree

abbrev BNode := Node 2

/-- Five-node witness to the failure of Remark 2 with the printed order. -/
def remark2Witness : List BNode :=
  [[],
   [(0 : Fin 2)],
   [(1 : Fin 2)],
   [(1 : Fin 2), (0 : Fin 2)],
   [(1 : Fin 2), (1 : Fin 2)]]

theorem remark2_semicomplete_printed :
    semiCompleteB paperAuxB remark2Witness = true := by
  decide

theorem remark2_interior_not_skew_printed :
    skewB paperAuxB (interior remark2Witness) = false := by
  decide

/-- Set-like equality for duplicate-free lists. -/
def sameMembers (A B : List BNode) : Bool :=
  A.all (fun x => decide (x ∈ B)) &&
    B.all (fun x => decide (x ∈ A))

def intersection (A B : List BNode) : List BNode :=
  A.filter (fun x => decide (x ∈ B))

def hasCompleteExtension
    (aux : BNode → BNode → Bool) (k : Nat)
    (S T Tprime : List BNode) : Bool :=
  S.sublists.any (fun A =>
    completeB aux k A &&
      sameMembers (intersection A T) Tprime)

/--
Concrete spliced tree used for the forward-lex audit of Remark 1.
-/
def forwardS : List BNode :=
  [[],
   [(0 : Fin 2)], [(1 : Fin 2)],
   [(0 : Fin 2), (0 : Fin 2)],
   [(0 : Fin 2), (1 : Fin 2)],
   [(1 : Fin 2), (0 : Fin 2)],
   [(1 : Fin 2), (1 : Fin 2)],
   [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)],
   [(0 : Fin 2), (0 : Fin 2), (1 : Fin 2)],
   [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
   [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]]

def forwardT : List BNode :=
  [[],
   [(0 : Fin 2)], [(1 : Fin 2)],
   [(0 : Fin 2), (0 : Fin 2)],
   [(0 : Fin 2), (1 : Fin 2)]]

def forwardTprime : List BNode :=
  [[],
   [(0 : Fin 2)], [(1 : Fin 2)],
   [(0 : Fin 2), (0 : Fin 2)]]

theorem forwardS_is_skew :
    skewB forwardAuxB forwardS = true := by
  decide

theorem forwardTprime_is_skew :
    skewB forwardAuxB forwardTprime = true := by
  decide

/--
The second assertion of Remark 1 fails even after replacing reverse lex by
forward lex.  All sublists of the eleven-node ambient tree are checked.
-/
theorem no_forward_complete_extension :
    hasCompleteExtension forwardAuxB 3 forwardS forwardT forwardTprime = false := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

end DualTree.GenericSkewAudit
