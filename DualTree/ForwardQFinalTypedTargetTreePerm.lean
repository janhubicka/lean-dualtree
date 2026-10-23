import DualTree.ForwardQFinalTypedTargetPreimage
import DualTree.ForwardQFinalTargetIntrinsicBands
import Mathlib.Data.Finset.Dedup

/-!
# Strengthen exact corrected Q target support equality to list permutation

A starred finite support is represented by a duplicate-free list of
homogeneous-tree nodes. The actual typed corrected Q construction uses
the arbitrary Finset.toList enumeration, whereas the requested target
O.tree comes with its own (equally legitimate) enumeration.

The existing proof identifies their FINITE NODE SETS. Since both
lists are duplicate-free as a consequence of their genuine
semi-complete-skew certificates, Mathlib's
List.perm_of_nodup_nodup_toFinset_eq now yields an exact LIST
PERMUTATION, not an unwarranted literal list equality.

This closes the representation-invariant tree-list comparison for
the corrected target preimage. No printed reverse-lex W_* domain
equivalence or Ramsey iteration statement is inferred.
-/

namespace DualTree.ForwardQFinalTypedTargetTreePerm

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- Under the exact corrected complete-signature and supported
target evaluated-span hypotheses, the actual full Q starred output
can be chosen as an element of the lifted local mixed-word span
with a tree list PERMUTATION of the requested target and with its
entire rooted dependent word identical up to the canonical
source/target variable-root equivalence.

The distinction between permutation and literal equality is
necessary because the two lists may have different enumerations;
it does not affect their finite support-tree structure. -/
theorem exists_typed_corrected_Q_target_tree_perm
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun a : α => a) fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ (ForwardQFinalMixedAlphabetSpan.mapMixedWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin (m + 1))))).span ∧
      List.Perm
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w).tree O.tree ∧
      ∀ s : BoundedNode b n,
        Sum.map id
          (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
            hb g O cutO H)
          ((ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w).word.word s) = O.word.word s := by
  classical
  obtain ⟨w, hwspan, hset, hword⟩ :=
    ForwardQFinalTypedTargetPreimage.exists_typed_corrected_Q_starred_target_preimage
      hb g f fallback O cutO H hα hspan hSupport σ
  let U := ForwardQAmbientFibreLegalWord.fibreQStarredWord
    hb g fallback w
  have hU : U.tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup U
  have hO : O.tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup O
  have hperm : List.Perm U.tree O.tree :=
    List.perm_of_nodup_nodup_toFinset_eq hU hO hset
  exact ⟨w, hwspan, hperm, hword⟩

end DualTree.ForwardQFinalTypedTargetTreePerm
