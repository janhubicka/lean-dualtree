import DualTree.ForwardQFinalTargetOrderFromSkew
import DualTree.ForwardQAmbientFibreLegalWord

/-!
# Actual typed corrected Q starred-object preimage of a supported target

The preceding theorem constructs a concrete enlarged input, proves
its correct starred-domain certificate (from the target's own skew
clauses), and identifies its corrected Q support and entire dependent
word with the desired target O.

Here we package that input as an actual EnlargedStarredInput subtype
and apply the existing FULL fibrewise fibreQStarredWord constructor.
This yields an actual StarredSignature.StarredWord, rather than just
separate raw nodes and fibreQSymbol expressions.

The target's finite tree is compared as a FINITE NODE SET: the Lean
representation chooses an arbitrary duplicate-free enumeration for
the Q support. The complete rooted variable-word map is equal after
the already verified canonical source/target root equivalence.

The theorem is still under the corrected forward auxiliary order.
It does not silently identify its W_* input domain with the printed
reverse-lex W_* domain, nor address the Ramsey colouring/induction
proof or the numerical parameter choices.
-/

namespace DualTree.ForwardQFinalTypedTargetPreimage

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The actual FINAL Q starred-word construction is surjective onto
the specified supported, complete-signature-equal target O, modulo
the unavoidable list representation of its finite tree and the
canonical bijection of dependent source/target root labels.

The witness is a genuinely TYPED corrected enlarged starred input,
belongs to the real alphabet-lifted local mixed-word span, and its
true completed Q starred-word has exactly the target node set and
dependent symbol function.

No independent D₂-order or target-rank-gap hypothesis remains. -/
theorem exists_typed_corrected_Q_starred_target_preimage
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
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree.toFinset = O.tree.toFinset ∧
      ∀ s : BoundedNode b n,
        Sum.map id
          (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
            hb g O cutO H)
          ((ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w).word.word s) = O.word.word s := by
  classical
  obtain ⟨w, hwspan, hwstar, htree, hword⟩ :=
    ForwardQFinalTargetOrderFromSkew.exists_coherent_starred_target_Q_preimage
      hb g f fallback O cutO H hα hspan hSupport σ
  let W : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback := ⟨w, hwstar⟩
  refine ⟨W, hwspan, ?_, ?_⟩
  · change
      (nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux
          g.core fallback w)).toList.toFinset = O.tree.toFinset
    simpa using htree
  · intro s
    change Sum.map id
      (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
        hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w s) = O.word.word s
    exact hword s

end DualTree.ForwardQFinalTypedTargetPreimage
