import DualTree.StarredSignature
import Mathlib

/-!
# Exceptional signature leaves after a branching cut

A semi-complete skew tree satisfies the skew construction's full-branching
condition before its last interior node. For a distinguished cut at which
fullBeforeB holds, every earlier node in the tree has at least one
immediate successor, so it cannot be a leaf.

This file proves that implication in the executable Section 3 definitions,
then uses it to totalize the Definition 26 signature boundary constructor
conditional only on fullBeforeB and membership of the cut in the interior.

The remaining proof obligation is to derive fullBeforeB at the actual
last interior node from semiCompleteB and the skew-tree axioms, rather
than treating it as an extra assumption.
-/

namespace DualTree.StarredSignature

/-- The executable direction enumeration has the correct length. -/
theorem allFin_length (b : Nat) :
    (SkewTree.allFin b).length = b := by
  induction b with
  | zero =>
      simp [SkewTree.allFin]
  | succ b ih =>
      simp [SkewTree.allFin, ih]

/-- A positive branching number has at least one available direction. -/
theorem allFin_nonempty {b : Nat} (hb : 0 < b) :
    ∃ i : Fin b, i ∈ SkewTree.allFin b := by
  cases hlist : SkewTree.allFin b with
  | nil =>
      have hl := allFin_length b
      rw [hlist] at hl
      simp at hl
      omega
  | cons i rest =>
      exact ⟨i, by simp [hlist]⟩

/-- Adding a further Boolean condition to an empty filter remains empty. -/
theorem filter_conj_eq_nil {β : Type*}
    (xs : List β) (p q : β → Bool)
    (hp : xs.filter p = []) :
    xs.filter (fun x => p x && q x) = [] := by
  have hfilter : ∀ ys : List β,
      ys.filter (fun x => p x && q x) =
        (ys.filter p).filter q := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x ys ih =>
        cases hx : p x <;> cases hq : q x <;>
          simp [List.filter_cons, hx, hq, ih]
  rw [hfilter xs, hp]
  rfl

/--
If every earlier node branches fully, no leaf in the tree is strictly before
the branching cut.
-/
theorem leaf_not_before_of_fullBefore
    {b : Nat} (hb : 0 < b)
    (S : List (Node b))
    (aux : Node b → Node b → Bool)
    (cut leaf : Node b)
    (hfull : SkewTree.fullBeforeB aux S cut = true)
    (hmem : leaf ∈ S)
    (hleaf : SkewTree.immediateSuccs S leaf = [])
    (hneq : leaf ≠ cut) :
    ¬ (aux leaf cut = true) := by
  intro hbefore
  obtain ⟨i, hi⟩ := allFin_nonempty hb
  have htest : aux leaf cut && !(leaf == cut) = true := by
    simp [hbefore, hneq]
  have hentry :
      (SkewTree.allFin b).all
        (fun j => SkewTree.uniqueBranchB S leaf j) = true := by
    have hh := (List.all_eq_true.mp hfull) leaf hmem
    simpa [hbefore, hneq] using hh
  have hbranch : SkewTree.uniqueBranchB S leaf i = true :=
    (List.all_eq_true.mp hentry) i hi
  have hcount : (SkewTree.branchWitnesses S leaf i).length = 1 := by
    simpa [SkewTree.uniqueBranchB] using hbranch
  have hnil : SkewTree.branchWitnesses S leaf i = [] := by
    unfold SkewTree.branchWitnesses
    exact filter_conj_eq_nil S
      (fun u => SkewTree.immediateSuccB S leaf u)
      (fun u => (leaf ++ [i]).isPrefixOf u)
      (by simpa [SkewTree.immediateSuccs] using hleaf)
  rw [hnil] at hcount
  simp at hcount

/-- A node of S not in its interior has no immediate successors. -/
theorem immediateSuccs_nil_of_not_interior {b : Nat}
    (S : List (Node b)) (t : Node b)
    (hmem : t ∈ S)
    (hout : t ∉ SkewTree.interior S) :
    SkewTree.immediateSuccs S t = [] := by
  cases hb : (SkewTree.immediateSuccs S t).isEmpty with
  | false =>
      have hinterior : t ∈ SkewTree.interior S := by
        simp [SkewTree.interior, hmem, hb]
      exact (hout hinterior).elim
  | true =>
      cases hs : SkewTree.immediateSuccs S t with
      | nil => rfl
      | cons s ss =>
          simp [hs] at hb

/--
Under the full-before condition at the distinguished interior cut,
every exceptional leaf selected in Definition 26 lies outside D.
-/
theorem exceptionalLeaves_not_before_of_fullBefore
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hfull : SkewTree.fullBeforeB SkewTree.paperAuxB
      O.tree cut = true)
    (t : Node b)
    (ht : t ∈ exceptionalLeaves O cut) :
    ¬ SignatureBoundary.BeforeCut cut t := by
  rcases exceptionalLeaves_spec O cut t ht with
    ⟨hmem, hnotInterior, hnotDescendant⟩
  have hleaf : SkewTree.immediateSuccs O.tree t = [] :=
    immediateSuccs_nil_of_not_interior O.tree t hmem hnotInterior
  have hneq : t ≠ cut := by
    intro h
    subst t
    exact hnotInterior hcut
  have hnotEarlier :=
    leaf_not_before_of_fullBefore hb O.tree
      SkewTree.paperAuxB cut t hfull hmem hleaf hneq
  intro htBefore
  apply hnotEarlier
  simpa [SkewTree.paperAuxB] using htBefore.1

/--
The source signature tree is now defined without per-leaf existence
assumptions, provided the last-interior node has the full-before property.
-/
noncomputable def signatureTree_of_fullBefore
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hfull : SkewTree.fullBeforeB SkewTree.paperAuxB
      O.tree cut = true) :
    List (Node b) :=
  signatureTree O cut
    (exceptionalLeaves_not_before_of_fullBefore hb O cut hcut hfull)

/-- All old interior vertices remain in the conditional signature tree. -/
theorem interior_mem_signatureTree_of_fullBefore
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hfull : SkewTree.fullBeforeB SkewTree.paperAuxB
      O.tree cut = true)
    {s : Node b}
    (hs : s ∈ SkewTree.interior O.tree) :
    s ∈ signatureTree_of_fullBefore hb O cut hcut hfull := by
  exact interior_mem_signatureTree O cut
    (exceptionalLeaves_not_before_of_fullBefore hb O cut hcut hfull) hs

end DualTree.StarredSignature
