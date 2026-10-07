import DualTree.BinarySkewAudit

/-!
# Remark 1: extension-clause counterexample

The order typo on p. 7 does not account for the second assertion of Remark 1.
This file certifies a finite counterexample using the candidate forward-lex
repair.

Take b = 2, n = 4, s = 01 and k = m = 1.  Then the initial segment T is

  {∅, 0, 1, 00, 01}.

With singleton tail components, the spliced tree S consists of T together with
the six prefix-minimal nodes outside T.  Let

  T' = {∅, 0, 1, 00}.

Both S and T' are skew under the forward-lex convention, but no 3-complete
skew subtree A of S has A ∩ T = T'.  Since S has eleven nodes, the final
statement can be checked by exhausting its 2^11 sublists.
-/

namespace DualTree.Remark1Audit

open BinarySkewAudit

def sameMembersB (A B : List BNode) : Bool :=
  A.all (fun x => decide (x ∈ B)) &&
    B.all (fun x => decide (x ∈ A))

def intersectionB (A B : List BNode) : List BNode :=
  A.filter (fun x => decide (x ∈ B))

/-- Binary version of k-completeness: all leaves have intrinsic height k-1
and every non-leaf has the two required immediate successors. -/
def completeB (aux : BNode → BNode → Bool) (k : Nat)
    (S : List BNode) : Bool :=
  skewB aux S &&
    S.all (fun s =>
      let d := (immediateSuccs S s).length
      if d = 0 then
        decide (heightAt S s + 1 = k)
      else
        decide (d = 2))

def hasCompleteExtensionB (aux : BNode → BNode → Bool) (k : Nat)
    (S T Tprime : List BNode) : Bool :=
  S.sublists.any (fun A =>
    completeB aux k A &&
      sameMembersB (intersectionB A T) Tprime)

/-- The spliced tree in the forward-lex counterexample. -/
def forwardS : List BNode :=
  [[],
   [false], [true],
   [false, false], [false, true], [true, false], [true, true],
   [false, false, false], [false, false, true],
   [false, true, false], [false, true, true]]

def forwardT : List BNode :=
  [[], [false], [true], [false, false], [false, true]]

def forwardTprime : List BNode :=
  [[], [false], [true], [false, false]]

theorem forwardS_is_skew :
    skewB forwardAuxB forwardS = true := by
  decide

theorem forwardTprime_is_skew :
    skewB forwardAuxB forwardTprime = true := by
  decide

/-- The second assertion of Remark 1 fails even after the forward-lex repair. -/
theorem no_forward_complete_extension :
    hasCompleteExtensionB forwardAuxB 3 forwardS forwardT forwardTprime = false := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide

end DualTree.Remark1Audit
