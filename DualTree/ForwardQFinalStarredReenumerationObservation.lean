import DualTree.ForwardQFinalStarredReenumeration

/-!
# Complete observations under starred-tree re-enumeration

The tree-node set and the full root-labelled word are unchanged by the
generic re-enumeration. This observation theorem is checked independently
of the subsequent complete-signature normalization construction.
-/

namespace DualTree.ForwardQFinalStarredReenumeration

/-- Re-enumeration preserves the full finite tree and rooted-word
observation, without any alphabet-cardinality assumption. -/
theorem reorderStarredWord_observe
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (T : List (Node b)) (hperm : T.Perm O.tree) :
    ForwardQFinalTargetObservation.observe (reorderStarredWord O T hperm) =
      ForwardQFinalTargetObservation.observe O := by
  classical
  unfold ForwardQFinalTargetObservation.observe
  apply Prod.ext
  · ext t
    simp only [List.mem_toFinset, reorderStarredWord_tree]
    exact hperm.mem_iff
  · funext s
    cases hw : O.word.word s with
    | inl a =>
        simp only [ForwardQSimpleLetterSmooth.rootLabel, reorderStarredWord_word, hw]
    | inr v =>
        simp only [ForwardQSimpleLetterSmooth.rootLabel, reorderStarredWord_word, hw]

end DualTree.ForwardQFinalStarredReenumeration
