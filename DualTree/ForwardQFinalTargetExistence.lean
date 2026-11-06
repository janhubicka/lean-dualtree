import DualTree.ForwardQFinalInducedSignature
import DualTree.ForwardQFinalInducedRefinement
import DualTree.ForwardQFinalInducedSupport
import DualTree.ForwardQFinalTargetHeightBoundary

/-!
# General existence of source-relative starred targets

For every genuine supplied local mixed word of height at least two,
the actual induced enlarged starred input gives a source-relative target
after fibrewise Q. This uses its complete set signature, a symbolic
substitution through the final word, and containment of every Q tree
vertex in the final support. Fixed auxiliary constants retain their
actual visible-ancestor decoding throughout.

Together with the height-one obstruction, this gives the exact positive
local-height threshold. The source-facing assembly now provides both an
inhabited target class and Q coverage of every eligible target. The local
mixed word is still supplied input; no local Ramsey existence or colour
control is asserted here.
-/

namespace DualTree.ForwardQFinalTargetExistence

open ForwardSourceQTree
open ForwardQSourceRefinement
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQFinalSetSpanTransfer
open ForwardQFinalTargetObservation

/-- Every induced enlarged starred input yields a genuine source-relative
target at local height at least two, for any assignment of original letters
to the final roots. Its complete signature includes the full strict domain. -/
theorem inducedQ_sourceRelativeSetTarget
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) (hq2 : 2 ≤ q) :
    SourceRelativeSetTarget hb g
      (enlargedInterpolatedFinalWord g f fallback)
      (ForwardQAmbientFibreLegalWord.fibreQStarredWord hb g fallback
        (enlargedInducedStarredInput g f fallback σ hq)) := by
  refine ⟨g.core.cut,
    ForwardQFinalInducedSignature.fibreQStarredWord_sameCompleteSetForwardSignature
      hb g fallback _,
    ForwardQFinalInducedRefinement.inducedQ_syntacticallyRefines_final
      hb g f fallback σ hq, ?_⟩
  exact ForwardQFinalInducedSupport.fibreQStarredWord_enlargedInduced_tree_subset_finalWordSupport
      hb g f fallback σ hq hq2

/-- A concrete target and its actual Q preimage exist for every supplied
local mixed word at height at least two. The input belongs to that word's
genuine enlarged span, with its fixed auxiliary constants unchanged. -/
theorem exists_sourceRelativeSetTarget_with_actual_Q_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq2 : 2 ≤ q) :
    ∃ (O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)))
      (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback),
      SourceRelativeSetTarget hb g
        (enlargedInterpolatedFinalWord g f fallback) O ∧
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  have hq : 0 < q := by omega
  let w := enlargedInducedStarredInput g f fallback (fun _ => fallback) hq
  refine ⟨ForwardQAmbientFibreLegalWord.fibreQStarredWord hb g fallback w,
    w, inducedQ_sourceRelativeSetTarget hb g f fallback
      (fun _ => fallback) hq hq2, ?_, rfl⟩
  exact enlargedInducedStarredInput_mem_span
    g f fallback (fun _ => fallback) hq

/-- The complete set-signature target class is inhabited for every actual
local mixed word at height at least two, over any alphabet with a fallback. -/
theorem sourceRelativeSetTarget_nonempty
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq2 : 2 ≤ q) :
    ∃ O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)),
      SourceRelativeSetTarget hb g
        (enlargedInterpolatedFinalWord g f fallback) O := by
  obtain ⟨O, _w, hO, _hw, _hQ⟩ :=
    exists_sourceRelativeSetTarget_with_actual_Q_preimage hb g f fallback hq2
  exact ⟨O, hO⟩

/-- Among positive local heights, two is the exact threshold for existence
of a starred target with the prescribed complete set signature. -/
theorem sourceRelativeSetTarget_nonempty_iff_two_le
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq : 0 < q) :
    (∃ O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)),
      SourceRelativeSetTarget hb g
        (enlargedInterpolatedFinalWord g f fallback) O) ↔ 2 ≤ q := by
  constructor
  · rintro ⟨O, hO⟩
    exact ForwardQFinalTargetHeightBoundary.sourceRelativeSetTarget_requires_two_local_levels
      hb g f fallback hq O hO
  · exact sourceRelativeSetTarget_nonempty hb g f fallback

/-- Construct the complete final word, prove its full initial-root contract,
exhibit a source-relative starred target, and cover every such target by Q. -/
theorem exists_complete_nonempty_set_source_relative_Q_transfer
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq2 : 2 ≤ q) :
    ∃ final : KVariableWord b n (m+q) α (SkewTree.forwardAuxB (b := b)),
      SyntacticallyRefines final.toVariableWord g.ambient ∧
      (∀ u : g.ambient.Vars, ForwardAux u.1.1 g.core.cut →
        u.1 ∈ final.toVariableWord.support) ∧
      (∀ s : BoundedNode b n, ForwardAux s.1 g.core.cut →
        CutPreservation.underlyingSymbol final.toVariableWord s =
          CutPreservation.underlyingSymbol g.ambient s) ∧
      final.span.Nonempty ∧
      (∃ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O) ∧
      ∀ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O →
        ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback,
          w.1 ∈ f.span ∧
          observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w) = observe O := by
  have hq : 0 < q := by omega
  refine ⟨enlargedInterpolatedFinalKWord g f fallback hb hq,
    enlargedFinal_syntacticallyRefines_ambient g f fallback,
    enlargedFinal_retains_initial_roots g f fallback,
    enlargedFinal_preserves_initial_symbols g f fallback,
    enlargedInterpolatedFinalKWord_span_nonempty g f fallback hb hq,
    sourceRelativeSetTarget_nonempty hb g f fallback hq2, ?_⟩
  intro O hO
  exact sourceRelativeSetTarget_has_Q_preimage hb g f fallback O hO

/-- The source-facing nonempty Q transfer derives the actual fibre frame
from the ambient support and the original source's symbolic refinement. -/
theorem exists_complete_nonempty_set_Q_transfer_of_source_refinement
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (core : Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hSource : SyntacticallyRefines core.source.word ambient)
    (f : LocalMixedWord core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hq2 : 2 ≤ q) :
    let g := fibreFrameOfSyntactic core ambient hsupport hSource
    ∃ final : KVariableWord b n (m+q) α (SkewTree.forwardAuxB (b := b)),
      SyntacticallyRefines final.toVariableWord ambient ∧
      (∀ u : ambient.Vars, ForwardAux u.1.1 core.cut →
        u.1 ∈ final.toVariableWord.support) ∧
      (∀ s : BoundedNode b n, ForwardAux s.1 core.cut →
        CutPreservation.underlyingSymbol final.toVariableWord s =
          CutPreservation.underlyingSymbol ambient s) ∧
      final.span.Nonempty ∧
      (∃ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O) ∧
      ∀ O : StarredSignature.StarredWord b n l α
          (SkewTree.forwardAuxB (b := b)),
        SourceRelativeSetTarget hb g final.toVariableWord O →
        ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput core fallback,
          w.1 ∈ f.span ∧
          observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w) = observe O := by
  exact exists_complete_nonempty_set_source_relative_Q_transfer hb
    (fibreFrameOfSyntactic core ambient hsupport hSource) f fallback hq2

end DualTree.ForwardQFinalTargetExistence
