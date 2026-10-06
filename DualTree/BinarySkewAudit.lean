import DualTree.OrderAudit

/-!
# Executable binary skew-tree audit

This file mirrors the finite clauses of Section 3 for binary trees.  It is
deliberately executable: before committing to the final abstract definition we
use it to certify the smallest source counterexamples found in the audit.

A later file will prove that this Boolean checker is equivalent to the
propositional skew-tree definition used by the main development.
-/

namespace DualTree.BinarySkewAudit

abbrev BNode := List Bool

def strictPrefixB (s t : BNode) : Bool :=
  s.isPrefixOf t && !(s == t)

def preds (S : List BNode) (s : BNode) : List BNode :=
  S.filter (fun t => strictPrefixB t s)

def heightAt (S : List BNode) (s : BNode) : Nat :=
  (preds S s).length

def immediateSuccB (S : List BNode) (s t : BNode) : Bool :=
  decide (t ∈ S) &&
    strictPrefixB s t &&
    !(S.any (fun u => strictPrefixB s u && strictPrefixB u t))

def immediateSuccs (S : List BNode) (s : BNode) : List BNode :=
  S.filter (fun t => immediateSuccB S s t)

def rootedB (S : List BNode) : Bool :=
  S.any (fun r => S.all (fun t => r.isPrefixOf t))

def condIIB (S : List BNode) : Bool :=
  S.all (fun s =>
    S.all (fun t =>
      if heightAt S s = heightAt S t ∧
          OrderAudit.boolLexLEB s t = true
      then decide (s.length ≤ t.length)
      else true))

def condIIIB (S : List BNode) : Bool :=
  S.all (fun s =>
    S.all (fun t =>
      if heightAt S s < heightAt S t
      then decide (s.length < t.length)
      else true))

def branchWitnesses (S : List BNode) (s : BNode) (i : Bool) : List BNode :=
  S.filter (fun t =>
    immediateSuccB S s t && (s ++ [i]).isPrefixOf t)

def uniqueBranchB (S : List BNode) (s : BNode) (i : Bool) : Bool :=
  (branchWitnesses S s i).length == 1

def dirsUpTo (iStar : Bool) : List Bool :=
  if iStar then [false, true] else [false]

def fullBeforeB (aux : BNode → BNode → Bool)
    (S : List BNode) (sStar : BNode) : Bool :=
  S.all (fun s =>
    if aux s sStar && !(s == sStar)
    then uniqueBranchB S s false && uniqueBranchB S s true
    else true)

def emptyAfterB (aux : BNode → BNode → Bool)
    (S : List BNode) (sStar : BNode) : Bool :=
  S.all (fun s =>
    if aux sStar s && !(s == sStar)
    then (immediateSuccs S s).isEmpty
    else true)

def partialAtB (S : List BNode) (sStar : BNode) (iStar : Bool) : Bool :=
  (immediateSuccs S sStar).length == (dirsUpTo iStar).length &&
    (dirsUpTo iStar).all (fun i => uniqueBranchB S sStar i)

def condIVB (aux : BNode → BNode → Bool) (S : List BNode) : Bool :=
  S.any (fun sStar =>
    [false, true].any (fun iStar =>
      fullBeforeB aux S sStar &&
      emptyAfterB aux S sStar &&
      partialAtB S sStar iStar))

def skewB (aux : BNode → BNode → Bool) (S : List BNode) : Bool :=
  rootedB S && condIIB S && condIIIB S && condIVB aux S

def semiCompleteB (aux : BNode → BNode → Bool) (S : List BNode) : Bool :=
  skewB aux S &&
    S.all (fun s =>
      let d := (immediateSuccs S s).length
      decide (d = 0 ∨ d = 2))

def interior (S : List BNode) : List BNode :=
  S.filter (fun s => !(immediateSuccs S s).isEmpty)

def paperAuxB (s t : BNode) : Bool :=
  decide (OrderAudit.paperAux s t)

def forwardAuxB (s t : BNode) : Bool :=
  decide (OrderAudit.forwardAux s t)

/-- The five-node source witness from the audit of Remark 2. -/
def remark2Witness : List BNode :=
  [[], [false], [true], [true, false], [true, true]]

theorem remark2_witness_is_semicomplete_printed :
    semiCompleteB paperAuxB remark2Witness = true := by
  decide

theorem remark2_interior_not_skew_printed :
    skewB paperAuxB (interior remark2Witness) = false := by
  decide

end DualTree.BinarySkewAudit
