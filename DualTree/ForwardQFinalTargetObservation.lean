import DualTree.ForwardQFinalTypedTargetTreePerm
import DualTree.ForwardQSimpleLetterSmooth

/-!
# Corrected Q target preimages as representation-independent observations

The actual starred Q-output tree is a duplicate-free list, but its
enumeration need not coincide with the target's arbitrary enumeration.
Its variable type is also a dependent subtype of the SOURCE support,
while the target variable type is a dependent subtype of the TARGET
support. These harmless representational differences prevent literal
equality of StarredWord records and arbitrary colour functions on records.

The true combinatorial observation is the finite support NODE SET
together with the complete tree word labelled by its genuine ROOTS,
not by proof-relevant dependent variable subtype elements. This file
packages the existing tree-permutation and fully reindexed word
preimage into equality of these observations.

The result is a precise interface for transferring colourings defined
on the actual unlabelled-by-enumeration combinatorial objects. It does
not assert that every arbitrary function on StarredWord records is
permutation-invariant, nor reconcile the printed reverse-lex W_*.
-/

namespace DualTree.ForwardQFinalTargetObservation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The representation-independent complete data of a rooted starred
tree word: its vertex SET and its entire ambient word with variable
names replaced by the actual bounded roots. -/
abbrev Observation (b n : Nat) (α : Type*) :=
  Finset (Node b) × (BoundedNode b n → Sum α (BoundedNode b n))

/-- Forget only irrelevant tree-list enumeration and subtype proofs
for variable roots; retain every vertex and every ambient word symbol. -/
noncomputable def observe
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Observation b n α := by
  classical
  exact (O.tree.toFinset, ForwardQSimpleLetterSmooth.rootLabel O)

/-- Equality of the entire DEPENDENT word after the canonical
source-to-target root equivalence implies equality of complete
root-labelled ambient words, not merely of their constant evaluations.
No alphabet-cardinality assumption is needed for this implication. -/
theorem rootLabel_Q_eq_target_of_word_reindexed
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback)
    (hword : ∀ s : BoundedNode b n,
      Sum.map id
        (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
          hb g O cutO H)
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w.1 s) = O.word.word s)
    (s : BoundedNode b n) :
    ForwardQSimpleLetterSmooth.rootLabel
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) s =
      ForwardQSimpleLetterSmooth.rootLabel O s := by
  let e := ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
    hb g O cutO H
  rw [ForwardQSimpleLetterSmooth.rootLabel_fibreQ hb g fallback w s]
  have hs := hword s
  cases hq : ForwardQAmbientFibreSymbol.fibreQSymbol
      g fallback w.1 s with
  | inl a =>
      have ho : O.word.word s = Sum.inl a := by
        simpa [hq] using hs.symm
      simp [ForwardQSimpleLetterSmooth.rootLabel, hq, ho]
  | inr v =>
      have ho : O.word.word s = Sum.inr (e v) := by
        simpa [hq, e] using hs.symm
      have hv :
          (e v).1 = v.1 :=
        ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv_root
          hb g O cutO H v
      simp [ForwardQSimpleLetterSmooth.rootLabel, hq, ho, hv]

/-- The already verified target-tree LIST PERMUTATION and dependent
word reindexing together give literal equality of the corrected
combinatorial observations. This is stronger than agreement of
evaluated words but weaker than the invalid equality of arbitrary
tree-list representations. -/
theorem observe_Q_eq_target_of_tree_perm_and_word_reindexed
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback)
    (htree : List.Perm
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree O.tree)
    (hword : ∀ s : BoundedNode b n,
      Sum.map id
        (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
          hb g O cutO H)
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w.1 s) = O.word.word s) :
    observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
      hb g fallback w) = observe O := by
  apply Prod.ext
  · exact List.toFinset_eq_of_perm _ _ htree
  · funext s
    exact rootLabel_Q_eq_target_of_word_reindexed
      hb g fallback O cutO H w hword s

/-- Every supported same-complete-signature target O in the
interpolated final word span has a TRUE corrected starred Q witness
in the lifted local mixed-product span with the same COMPLETE
representation-independent observation. The extra D₂ length/order
hypothesis has already been discharged from target skewness. -/
theorem exists_starred_Q_observation_preimage
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
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  obtain ⟨w, hwspan, htree, hword⟩ :=
    ForwardQFinalTypedTargetTreePerm.exists_typed_corrected_Q_target_tree_perm
      hb g f fallback O cutO H hα hspan hSupport σ
  refine ⟨w, hwspan, ?_⟩
  exact observe_Q_eq_target_of_tree_perm_and_word_reindexed
    hb g fallback O cutO H w htree hword

end DualTree.ForwardQFinalTargetObservation
