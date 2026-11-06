import DualTree.ForwardQFinalSyntacticSpanTransfer
import DualTree.ForwardQFinalSetSignatureReenumeration

/-!
# Source-relative Q transfer for the actual finite-set signature

The tree component of the paper's signature is a set. This module removes
the extra literal-list agreement from the earlier source-relative target
interface while retaining its full rooted partial word, syntactic word
refinement, and containment of every target tree vertex in the final
support.

A target is re-enumerated into the existing literal-signature interface.
Its variable word is unchanged and its tree changes only by permutation,
so its complete tree-and-rooted-word observation is unchanged. The actual
enlarged Q-preimage construction then applies with no new geometric,
alphabet-cardinality, or order hypothesis.

The complete final-word assembly retains every ambient root through the
cut, preserves the initial word, and covers all targets with this actual
set-valued complete signature. The local mixed word remains supplied
input; this is the Q-transfer step, not a local Ramsey existence theorem.
-/

namespace DualTree.ForwardQFinalSetSpanTransfer

open ForwardSourceQTree
open ForwardQSourceRefinement
open ForwardQFinalRefinementRoots
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalSetSignature
open ForwardQFinalSyntacticSpanTransfer
open ForwardQFinalTargetObservation

/-- The source-relative target class with the signature tree treated as
the actual finite node set. The partial word still records its full strict
domain, and containment covers terminal leaves as well as variable roots. -/
def SourceRelativeSetTarget
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (final : VariableWord b n α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  ∃ cutO : Node b,
    SameCompleteSetForwardSignature hb g O cutO ∧
    SyntacticallyRefines O.word final ∧
    (∀ t : Node b, t ∈ O.tree → t ∈ final.supportNodes)

/-- The existing literal-signature target interface remains a sufficient
special case of the actual set-signature target class. -/
theorem sourceRelativeSetTarget_of_literal
    {b n l k m : Nat} {α : Type*}
    {hb : 0 < b}
    {g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α}
    {final : VariableWord b n α}
    {O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))}
    (hO : SourceRelativeTarget hb g final O) :
    SourceRelativeSetTarget hb g final O := by
  obtain ⟨cutO, H, hRef, hTree⟩ := hO
  exact ⟨cutO, of_sameCompleteForwardSignature H, hRef, hTree⟩

private theorem observe_eq_of_word_eq_tree_perm
    {b n l : Nat} {α : Type*}
    (O' O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hword : O'.word = O.word) (hperm : O'.tree.Perm O.tree) :
    observe O' = observe O := by
  classical
  change (O'.tree.toFinset, CutPreservation.underlyingSymbol O'.word) =
    (O.tree.toFinset, CutPreservation.underlyingSymbol O.word)
  rw [hword]
  exact congrArg
    (fun T : Finset (Node b) => (T, CutPreservation.underlyingSymbol O.word))
    (List.toFinset_eq_of_perm O'.tree O.tree hperm)

/-- Every target with the actual complete set signature has a genuine
enlarged starred Q preimage in the supplied local mixed span. The support
premise needed for re-enumeration is derived from the final support. -/
theorem sourceRelativeSetTarget_has_Q_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : SourceRelativeSetTarget hb g
      (enlargedInterpolatedFinalWord g f fallback) O) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  obtain ⟨cutO, H, hRef, hTree⟩ := hO
  have hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T := by
    intro t ht
    apply ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
      g.core f (m+q) t
    exact (enlargedInterpolatedFinalWord_supportNodes_iff
      g f fallback t).1 (hTree t ht)
  obtain ⟨O', hword, hperm, H'⟩ :=
    ForwardQFinalSetSignatureReenumeration.exists_literal_reenumeration
      hb g O cutO H hT
  have hO' : SourceRelativeTarget hb g
      (enlargedInterpolatedFinalWord g f fallback) O' := by
    refine ⟨g.core.cut, H', ?_, ?_⟩
    · rw [hword]
      exact hRef
    · intro t ht
      exact hTree t (hperm.mem_iff.mp ht)
  obtain ⟨w, hw, hQ⟩ := sourceRelativeTarget_has_Q_preimage
    hb g f fallback O' hO'
  exact ⟨w, hw, hQ.trans (observe_eq_of_word_eq_tree_perm O' O hword hperm)⟩

/-- The correctly directed Q-image inclusion for fixed-signature
starred targets, independent of their tree-list enumerations. -/
theorem sourceRelativeSetTarget_observations_subset_Q_image
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    (observe '' {O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) |
      SourceRelativeSetTarget hb g
        (enlargedInterpolatedFinalWord g f fallback) O}) ⊆
    {o | ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = o} := by
  rintro o ⟨O, hO, rfl⟩
  exact sourceRelativeSetTarget_has_Q_preimage hb g f fallback O hO

/-- Construct a complete final word with the full source-relative
initial-root contract and Q coverage for the actual set-signature target
class. No chosen enumeration, extra D2 order, or matching witness is input. -/
theorem exists_complete_set_source_relative_Q_transfer
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq : 0 < q) :
    ∃ final : KVariableWord b n (m+q) α (SkewTree.forwardAuxB (b := b)),
      SyntacticallyRefines final.toVariableWord g.ambient ∧
      (∀ u : g.ambient.Vars, ForwardAux u.1.1 g.core.cut →
        u.1 ∈ final.toVariableWord.support) ∧
      (∀ s : BoundedNode b n, ForwardAux s.1 g.core.cut →
        CutPreservation.underlyingSymbol final.toVariableWord s =
          CutPreservation.underlyingSymbol g.ambient s) ∧
      final.span.Nonempty ∧
      ∀ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O →
        ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback,
          w.1 ∈ f.span ∧
          observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w) = observe O := by
  refine ⟨enlargedInterpolatedFinalKWord g f fallback hb hq,
    enlargedFinal_syntacticallyRefines_ambient g f fallback,
    enlargedFinal_retains_initial_roots g f fallback,
    enlargedFinal_preserves_initial_symbols g f fallback,
    enlargedInterpolatedFinalKWord_span_nonempty g f fallback hb hq, ?_⟩
  intro O hO
  exact sourceRelativeSetTarget_has_Q_preimage hb g f fallback O hO

/-- The source-facing assembly derives its fibre frame from the actual
ambient support and source substitution, then gives the complete final
word and transfer for the mathematical set-valued signature. -/
theorem exists_complete_set_Q_transfer_of_source_refinement
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (core : Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hSource : SyntacticallyRefines core.source.word ambient)
    (f : LocalMixedWord core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq : 0 < q) :
    let g := fibreFrameOfSyntactic core ambient hsupport hSource
    ∃ final : KVariableWord b n (m+q) α (SkewTree.forwardAuxB (b := b)),
      SyntacticallyRefines final.toVariableWord ambient ∧
      (∀ u : ambient.Vars, ForwardAux u.1.1 core.cut →
        u.1 ∈ final.toVariableWord.support) ∧
      (∀ s : BoundedNode b n, ForwardAux s.1 core.cut →
        CutPreservation.underlyingSymbol final.toVariableWord s =
          CutPreservation.underlyingSymbol ambient s) ∧
      final.span.Nonempty ∧
      ∀ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O →
        ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput core fallback,
          w.1 ∈ f.span ∧
          observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w) = observe O := by
  exact exists_complete_set_source_relative_Q_transfer hb
    (fibreFrameOfSyntactic core ambient hsupport hSource) f fallback hq

end DualTree.ForwardQFinalSetSpanTransfer
