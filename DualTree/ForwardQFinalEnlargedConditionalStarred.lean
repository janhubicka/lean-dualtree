import DualTree.ForwardQFinalEnlargedTargetWholeWord
import DualTree.ForwardQFinalTargetObservation

/-!
# The final conditional corrected starred target preimage, enlarged alphabet

The genuine post-Corollary-22 local word has its full enlarged alphabet
α ⊕ Fin(m+1). We have now constructed an ACTUAL mixed-span input
reconstructing the requested target O's exact finite Q node set and
EVERY dependent rooted word symbol.

The exact remaining local admissibility requirement is the global
sorted D₂ singleton-vector order on this PARTICULAR target-selected
tuple of marked points. Conditional on that *precise* order, we
package the raw witness as an actual enlarged starred input and
apply the completed genuine fibrewise Q constructor.

The resulting Q is a real StarredSignature.StarredWord with exact
target tree-list permutation and full variable-word equality under
canonical source/target root transport. In particular its
representation-independent tree-and-rooted-word observation equals
that of O, with a witness in the genuine enlarged mixed Ramsey span.

This theorem does NOT derive the D₂ order, transport the printed
reverse-lex W_* to the repaired forward-starred domain, or supply
the numerical Corollary-22 Ramsey word. Those are explicit separate
obligations. This isolates the geometric last step honestly.
-/

namespace DualTree.ForwardQFinalEnlargedConditionalStarred

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalEnlargedTargetInput
open ForwardQFinalEnlargedTargetWholeWord
open ForwardQFinalTargetObservation

/-- The EXACT outstanding corrected starred-domain condition on the
target-selected enlarged local mixed span point, with no reliance
on arbitrary D₂-coordinate reindexing or source paper W_*. -/
def TargetD2Ordered
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) : Prop :=
  ForwardQIndexedTRanks.BulletLengthsOrdered g.core
    (ForwardQEnlargedConstantWords.eraseAux g.core fallback
      (coherentTargetInput hb g f fallback O cutO H hSupport))

/-- A certified sorted D₂ point-length order promotes the actual
coherent enlarged mixed-span target input to the corrected starred
subtype. Its D₂ points and coordinate words remain unchanged. -/
theorem coherentTargetInput_isStarred_of_order
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (hOrder : TargetD2Ordered hb g f fallback O cutO H hSupport) :
    ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback
        (coherentTargetInput hb g f fallback O cutO H hSupport)) :=
  (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
    g.core _).2 hOrder

/-- Conditional on precisely the local sorted-D₂ admissibility,
EVERY supported same-complete-signature target O whose word span
refines the newly constructed genuinely enlarged f' word has an
ACTUAL typed corrected starred-Q preimage in the REAL enlarged
mixed Ramsey span, with the same complete tree-and-word
combinatorial observation.

The previously verified exact node-set, full word and local-span
results are used without strengthening the hypothesis to an
unrestricted independent final-root span reverse inclusion. -/
theorem exists_typed_enlarged_target_observation_preimage_of_order
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (hOrder : TargetD2Ordered hb g f fallback O cutO H hSupport) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  classical
  let raw := coherentTargetInput hb g f fallback O cutO H hSupport
  have hstar :
      ForwardQActualStarredSpace.IsStarred g.core
        (ForwardQEnlargedConstantWords.eraseAux g.core fallback raw) :=
    coherentTargetInput_isStarred_of_order
      hb g f fallback O cutO H hSupport hOrder
  let w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback := ⟨raw,hstar⟩
  have hwspan : raw ∈ f.span :=
    coherentTargetInput_mem_mixed_span
      hb g f fallback O cutO H hSupport
  have htree :
      nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux
          g.core fallback raw) = O.tree.toFinset :=
    ForwardQFinalGenericTargetNodeSet.coherent_enlarged_target_Q_node_set_eq
      hb g f fallback O cutO H hSupport
  have hword :
      ∀ s : BoundedNode b n,
        Sum.map id
          (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
            hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback raw s) = O.word.word s :=
    coherent_target_Q_matches_full_word
      hb g f fallback O cutO H hα hspan hSupport
  have hset :
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree.toFinset = O.tree.toFinset := by
    change
      (nodes g.core
        (ForwardQEnlargedConstantWords.eraseAux
          g.core fallback raw)).toList.toFinset = O.tree.toFinset
    simpa using htree
  have hU :
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w).tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w)
  have hO : O.tree.Nodup :=
    ForwardQFinalTargetIntrinsicBands.target_tree_nodup O
  have hperm :
      List.Perm
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w).tree O.tree :=
    List.perm_of_nodup_nodup_toFinset_eq hU hO hset
  have hwordQ :
      ∀ s : BoundedNode b n,
        Sum.map id
          (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
            hb g O cutO H)
          ((ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w).word.word s) = O.word.word s := by
    intro s
    change Sum.map id
      (ForwardQFinalFullSignatureRootTransport.sourceOutputVarsEquiv
        hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback raw s) = O.word.word s
    exact hword s
  refine ⟨w,hwspan,?_⟩
  exact observe_Q_eq_target_of_tree_perm_and_word_reindexed
    hb g fallback O cutO H w hperm hwordQ

end DualTree.ForwardQFinalEnlargedConditionalStarred
