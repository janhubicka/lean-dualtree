import DualTree.NodeOrder

/-!
# Executable source-facing skew-tree definitions

This is the generic finite version of Section 3. A finite subtree is stored as
a duplicate-free list of nodes. The definitions are Boolean on purpose: the
paper is finite at this stage, and executable definitions let us certify small
counterexamples in the kernel while retaining a proposition-facing wrapper.

The auxiliary order is a parameter. Thus both the order printed on p. 7 and
the candidate forward-lex repair can be used with the same skew-tree clauses.

The paper explicitly adds singleton trees to the skew class after clauses
(i)--(iv); skewB includes that convention.
-/

namespace DualTree.SkewTree

/-- Enumerate all elements of Fin b in increasing order. -/
def allFin : (b : Nat) → List (Fin b)
  | 0 => []
  | b + 1 => (allFin b).map Fin.castSucc ++ [Fin.last b]

def strictPrefixB {b : Nat} (s t : Node b) : Bool :=
  s.isPrefixOf t && !(s == t)

def preds {b : Nat} (S : List (Node b)) (s : Node b) : List (Node b) :=
  S.filter (fun t => strictPrefixB t s)

def heightAt {b : Nat} (S : List (Node b)) (s : Node b) : Nat :=
  (preds S s).length

def immediateSuccB {b : Nat}
    (S : List (Node b)) (s t : Node b) : Bool :=
  decide (t ∈ S) &&
    strictPrefixB s t &&
    !(S.any (fun u => strictPrefixB s u && strictPrefixB u t))

def immediateSuccs {b : Nat}
    (S : List (Node b)) (s : Node b) : List (Node b) :=
  S.filter (fun t => immediateSuccB S s t)

def rootedB {b : Nat} (S : List (Node b)) : Bool :=
  S.any (fun r => S.all (fun t => r.isPrefixOf t))

/-- Clause (ii) of the printed skew-tree definition. -/
def condIIB {b : Nat} (S : List (Node b)) : Bool :=
  S.all (fun s =>
    S.all (fun t =>
      if heightAt S s = heightAt S t ∧ FinLexLE s t
      then decide (s.length ≤ t.length)
      else true))

/-- Clause (iii) of the printed skew-tree definition. -/
def condIIIB {b : Nat} (S : List (Node b)) : Bool :=
  S.all (fun s =>
    S.all (fun t =>
      if heightAt S s < heightAt S t
      then decide (s.length < t.length)
      else true))

def branchWitnesses {b : Nat}
    (S : List (Node b)) (s : Node b) (i : Fin b) : List (Node b) :=
  S.filter (fun t =>
    immediateSuccB S s t && (s ++ [i]).isPrefixOf t)

def uniqueBranchB {b : Nat}
    (S : List (Node b)) (s : Node b) (i : Fin b) : Bool :=
  (branchWitnesses S s i).length == 1

def dirsUpTo {b : Nat} (iStar : Fin b) : List (Fin b) :=
  (allFin b).filter (fun i => decide (i ≤ iStar))

def fullBeforeB {b : Nat}
    (aux : Node b → Node b → Bool)
    (S : List (Node b)) (sStar : Node b) : Bool :=
  S.all (fun s =>
    if aux s sStar && !(s == sStar)
    then (allFin b).all (fun i => uniqueBranchB S s i)
    else true)

def emptyAfterB {b : Nat}
    (aux : Node b → Node b → Bool)
    (S : List (Node b)) (sStar : Node b) : Bool :=
  S.all (fun s =>
    if aux sStar s && !(s == sStar)
    then (immediateSuccs S s).isEmpty
    else true)

def partialAtB {b : Nat}
    (S : List (Node b)) (sStar : Node b) (iStar : Fin b) : Bool :=
  (immediateSuccs S sStar).length == iStar.val + 1 &&
    (dirsUpTo iStar).all (fun i => uniqueBranchB S sStar i)

/-- Clause (iv), parameterized by the chosen auxiliary order. -/
def condIVB {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Bool :=
  S.any (fun sStar =>
    (allFin b).any (fun iStar =>
      fullBeforeB aux S sStar &&
      emptyAfterB aux S sStar &&
      partialAtB S sStar iStar))

/-- Clauses (i)--(iv), before the paper's explicit singleton convention. -/
def skewCoreB {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Bool :=
  decide S.Nodup &&
    rootedB S &&
    condIIB S &&
    condIIIB S &&
    condIVB aux S

/-- Skew tree, including the paper's convention that singletons are skew. -/
def skewB {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Bool :=
  decide S.Nodup &&
    ((S.length == 1) ||
      (rootedB S && condIIB S && condIIIB S && condIVB aux S))

/-- Proposition-facing wrapper around the executable skew definition. -/
def Skew {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Prop :=
  skewB aux S = true

/-- Semi-complete means skew and every non-leaf has exactly b immediate successors. -/
def semiCompleteB {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Bool :=
  skewB aux S &&
    S.all (fun s =>
      let d := (immediateSuccs S s).length
      decide (d = 0 ∨ d = b))

def SemiComplete {b : Nat}
    (aux : Node b → Node b → Bool) (S : List (Node b)) : Prop :=
  semiCompleteB aux S = true

/-- k-complete: every leaf is at intrinsic level k-1, and every non-leaf
has all b immediate successors. -/
def completeB {b : Nat}
    (aux : Node b → Node b → Bool) (k : Nat)
    (S : List (Node b)) : Bool :=
  skewB aux S &&
    S.all (fun s =>
      let d := (immediateSuccs S s).length
      if d = 0 then
        decide (heightAt S s + 1 = k)
      else
        decide (d = b))

def Complete {b : Nat}
    (aux : Node b → Node b → Bool) (k : Nat)
    (S : List (Node b)) : Prop :=
  completeB aux k S = true

def interior {b : Nat} (S : List (Node b)) : List (Node b) :=
  S.filter (fun s => !(immediateSuccs S s).isEmpty)

def paperAuxB {b : Nat} (s t : Node b) : Bool :=
  decide (PaperAux s t)

def forwardAuxB {b : Nat} (s t : Node b) : Bool :=
  decide (ForwardAux s t)

theorem singleton_skewB {b : Nat}
    (aux : Node b → Node b → Bool) (s : Node b) :
    skewB aux [s] = true := by
  simp [skewB]

theorem singleton_complete_oneB {b : Nat}
    (aux : Node b → Node b → Bool) (s : Node b) :
    completeB aux 1 [s] = true := by
  simp [completeB, skewB, immediateSuccs, immediateSuccB, strictPrefixB,
    heightAt, preds]

end DualTree.SkewTree
