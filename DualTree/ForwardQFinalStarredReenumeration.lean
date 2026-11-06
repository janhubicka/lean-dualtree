import DualTree.ForwardQFinalTargetObservation

/-!
# Re-enumerating a starred tree without changing its word

A starred support is represented by a duplicate-free list. Its skew and
semi-complete conditions depend on the node set and intrinsic tree ranks,
not on the order of that list. This module transports those conditions
along an actual list permutation and changes only the tree field of a
starred word.

The variable word, including its own support enumeration and dependent
variable type, is definitionally unchanged. The complete tree-and-word
observation is therefore unchanged as well. No literal signature-list
equality is inferred here: arranging a particular signature enumeration
requires a separate construction.
-/

namespace DualTree.ForwardQFinalStarredReenumeration

private theorem heightAt_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    SkewTree.heightAt S s = SkewTree.heightAt T s := by
  exact (List.Perm.filter (fun t => SkewTree.strictPrefixB t s) h).length_eq

/-- Immediate-successor membership is independent of the enumeration
of the surrounding finite tree. -/
theorem immediateSuccB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s t : Node b) :
    SkewTree.immediateSuccB S s t = SkewTree.immediateSuccB T s t := by
  simp only [SkewTree.immediateSuccB, h.mem_iff, h.any_eq]

/-- The actual immediate-successor lists change by permutation. -/
theorem immediateSuccs_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).Perm (SkewTree.immediateSuccs T s) := by
  have hp : SkewTree.immediateSuccB S s = SkewTree.immediateSuccB T s :=
    funext (immediateSuccB_eq_of_perm h s)
  unfold SkewTree.immediateSuccs
  rw [hp]
  exact List.Perm.filter _ h

private theorem immediateSuccs_length_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).length =
      (SkewTree.immediateSuccs T s).length :=
  (immediateSuccs_perm h s).length_eq

private theorem immediateSuccs_isEmpty_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).isEmpty =
      (SkewTree.immediateSuccs T s).isEmpty :=
  (immediateSuccs_perm h s).isEmpty_eq

/-- Interior lists inherit the support permutation. -/
theorem interior_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) :
    (SkewTree.interior S).Perm (SkewTree.interior T) := by
  have hp :
      (fun s => !(SkewTree.immediateSuccs S s).isEmpty) =
        (fun s => !(SkewTree.immediateSuccs T s).isEmpty) := by
    funext s
    rw [immediateSuccs_isEmpty_eq_of_perm h s]
  unfold SkewTree.interior
  rw [hp]
  exact List.Perm.filter _ h

/-- Interior membership is a property of the finite tree, not its list. -/
theorem interior_mem_iff_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    s ∈ SkewTree.interior S ↔ s ∈ SkewTree.interior T :=
  (interior_perm h).mem_iff

private theorem branchWitnesses_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (s : Node b) (i : Fin b) :
    (SkewTree.branchWitnesses S s i).Perm
      (SkewTree.branchWitnesses T s i) := by
  have hp : SkewTree.immediateSuccB S s = SkewTree.immediateSuccB T s :=
    funext (immediateSuccB_eq_of_perm h s)
  unfold SkewTree.branchWitnesses
  rw [hp]
  exact List.Perm.filter _ h

private theorem uniqueBranchB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (s : Node b) (i : Fin b) :
    SkewTree.uniqueBranchB S s i = SkewTree.uniqueBranchB T s i := by
  unfold SkewTree.uniqueBranchB
  rw [(branchWitnesses_perm h s i).length_eq]

/-- All skew-tree clauses are preserved by re-enumeration, for either
auxiliary-order convention or any other supplied Boolean relation. -/
theorem skewB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (aux : Node b → Node b → Bool) :
    SkewTree.skewB aux S = SkewTree.skewB aux T := by
  have hroot : SkewTree.rootedB S = SkewTree.rootedB T := by
    simp only [SkewTree.rootedB, h.all_eq, h.any_eq]
  have hII : SkewTree.condIIB S = SkewTree.condIIB T := by
    simp only [SkewTree.condIIB, heightAt_eq_of_perm h, h.all_eq]
  have hIII : SkewTree.condIIIB S = SkewTree.condIIIB T := by
    simp only [SkewTree.condIIIB, heightAt_eq_of_perm h, h.all_eq]
  have hbefore : ∀ s, SkewTree.fullBeforeB aux S s =
      SkewTree.fullBeforeB aux T s := by
    intro s
    simp only [SkewTree.fullBeforeB, uniqueBranchB_eq_of_perm h, h.all_eq]
  have hafter : ∀ s, SkewTree.emptyAfterB aux S s =
      SkewTree.emptyAfterB aux T s := by
    intro s
    simp only [SkewTree.emptyAfterB, immediateSuccs_isEmpty_eq_of_perm h,
      h.all_eq]
  have hat : ∀ s i, SkewTree.partialAtB S s i =
      SkewTree.partialAtB T s i := by
    intro s i
    simp only [SkewTree.partialAtB, immediateSuccs_length_eq_of_perm h,
      uniqueBranchB_eq_of_perm h]
  have hIV : SkewTree.condIVB aux S = SkewTree.condIVB aux T := by
    simp only [SkewTree.condIVB, hbefore, hafter, hat, h.any_eq]
  simp only [SkewTree.skewB, h.nodup_iff, h.length_eq, hroot, hII, hIII, hIV]

/-- Semi-completeness is preserved along an actual tree-list permutation. -/
theorem semiCompleteB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (aux : Node b → Node b → Bool) :
    SkewTree.semiCompleteB aux S = SkewTree.semiCompleteB aux T := by
  simp only [SkewTree.semiCompleteB, skewB_eq_of_perm h,
    immediateSuccs_length_eq_of_perm h, h.all_eq]

/-- Give a corrected starred word another enumeration of the same
tree. Its entire variable-word field is definitionally unchanged. -/
def reorderStarredWord
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) where
  tree := T
  tree_bounded := fun t ht => O.tree_bounded t (hperm.mem_iff.mp ht)
  semi_complete :=
    (semiCompleteB_eq_of_perm hperm SkewTree.forwardAuxB).trans O.semi_complete
  word := O.word
  interior_card := (interior_perm hperm).length_eq.trans O.interior_card
  support_eq_interior := fun t =>
    (O.support_eq_interior t).trans (interior_mem_iff_of_perm hperm t).symm
  support_skew := O.support_skew

@[simp] theorem reorderStarredWord_tree
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    (reorderStarredWord O T hperm).tree = T := rfl

@[simp] theorem reorderStarredWord_word
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    (reorderStarredWord O T hperm).word = O.word := rfl

theorem reorderStarredWord_tree_perm
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    (reorderStarredWord O T hperm).tree.Perm O.tree := hperm

theorem reorderStarredWord_interior_perm
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    (SkewTree.interior (reorderStarredWord O T hperm).tree).Perm
      (SkewTree.interior O.tree) :=
  interior_perm hperm

theorem reorderStarredWord_interior_mem_iff
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) (s : Node b) :
    s ∈ SkewTree.interior (reorderStarredWord O T hperm).tree ↔
      s ∈ SkewTree.interior O.tree :=
  interior_mem_iff_of_perm hperm s

end DualTree.ForwardQFinalStarredReenumeration
