import DualTree.ForwardQFinalEnlargedCompleteWord
import DualTree.ForwardQFinalEnlargedPairwiseTransfer
import DualTree.ForwardQFinalInitialRootRetention

/-!
# Corrected Q transfer for source-relative syntactic refinements

The inclusion required by the fixed-signature step concerns starred
variable words, together with their whole tree support. It is not the
unrestricted evaluated constant-word span of the final interpolation.

This module states that target class using the actual final variable
word. The word component must be a uniform syntactic refinement, and
every target tree vertex, including terminal leaves, must belong to the
final support. The complete corrected signature is retained explicitly.
For alphabets with two distinct letters this is equivalent to the
existing evaluated-span target predicate. The syntactic form also works
for singleton alphabets.

Given any genuine enlarged local mixed variable word of positive height,
the construction produces an actual complete final word refining the
original ambient word, retaining all original roots through the cut and
preserving every symbol on that inclusive initial segment. Every
source-relative target has a corrected
starred Q preimage in the supplied local mixed span. Fixed auxiliary
constants and the target's D2 order are handled by the proved construction;
neither is an additional hypothesis.

The existence of a local Ramsey word with the needed colour property and
the identification with the printed reverse-lex order remain separate.
-/

namespace DualTree.ForwardQFinalSyntacticSpanTransfer

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQSourceRefinement
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalTargetObservation

/-- The corrected fixed-signature target class relative to an actual
ambient variable word. Tree containment includes terminal leaves, which
are not controlled by substitution of the interior variable roots. -/
def SourceRelativeTarget
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (final : VariableWord b n α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  ∃ cutO : Node b,
    ForwardQFinalFullSignature.SameCompleteForwardSignature hb g O cutO ∧
    SyntacticallyRefines O.word final ∧
    (∀ t : Node b, t ∈ O.tree → t ∈ final.supportNodes)

/-- Over a nondegenerate alphabet this precise symbolic target class
agrees with the earlier evaluated-span class. The equivalence also
identifies the actual final word's support with the rank-filtered set. -/
theorem sourceRelativeTarget_iff_eligibleEnlargedTarget
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    SourceRelativeTarget hb g (enlargedInterpolatedFinalWord g f fallback) O ↔
      ForwardQFinalEnlargedPairwiseTransfer.EligibleEnlargedTarget
        hb g f fallback O := by
  constructor
  · rintro ⟨cutO, H, hRef, hTree⟩
    refine ⟨cutO, H, hRef.span_subset, ?_⟩
    intro t ht
    exact (enlargedInterpolatedFinalWord_supportNodes_iff
      g f fallback t).1 (hTree t ht)
  · rintro ⟨cutO, H, hspan, hTree⟩
    refine ⟨cutO, H,
      (syntacticallyRefines_iff_span_subset hα O.word
        (enlargedInterpolatedFinalWord g f fallback)).2 hspan, ?_⟩
    intro t ht
    exact (enlargedInterpolatedFinalWord_supportNodes_iff
      g f fallback t).2 (hTree t ht)

/-- Every actual source-relative symbolic target has a genuine Q
preimage in the supplied enlarged mixed span. No assumption on the
number of original alphabet letters or extra D2-order premise is used. -/
theorem sourceRelativeTarget_has_Q_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hO : SourceRelativeTarget hb g
      (enlargedInterpolatedFinalWord g f fallback) O) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = observe O := by
  obtain ⟨cutO, H, hRef, hTree⟩ := hO
  have hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport g.core f (m+q) := by
    intro t ht
    exact (enlargedInterpolatedFinalWord_supportNodes_iff
      g f fallback t).1 (hTree t ht)
  exact ForwardQFinalEnlargedTargetD2Order.exists_typed_enlarged_target_observation_preimage_of_syntactic_refinement
      hb g f fallback O cutO H hRef hSupport

/-- The exact fixed-signature Q-image inclusion needed for transfer.
The left side consists of tree-and-rooted-word observations of eligible
starred targets; it is not the final word's evaluated constant span. -/
theorem sourceRelativeTarget_observations_subset_Q_image
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    (observe '' {O : StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) |
      SourceRelativeTarget hb g (enlargedInterpolatedFinalWord g f fallback) O}) ⊆
    {o | ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ f.span ∧
      observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
        hb g fallback w) = o} := by
  rintro o ⟨O, hO, rfl⟩
  exact sourceRelativeTarget_has_Q_preimage hb g f fallback O hO

/-- The enlarged interpolation is a syntactic refinement of the real
ambient word over every alphabet, with the actual global substitution. -/
theorem enlargedFinal_syntacticallyRefines_ambient
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    SyntacticallyRefines (enlargedInterpolatedFinalWord g f fallback)
      g.ambient :=
  ⟨enlargedGlobalRootSymbol g f fallback, rfl⟩

/-- Construct a genuine complete final word with the correctly directed
ambient refinement, retention of all ambient roots through the cut,
preservation of every initial symbol, a real nonempty evaluated span, and
coverage of all source-relative starred targets by corrected Q of the
local mixed span.

The local mixed word is input data; this theorem constructs the Q transfer,
not a local Ramsey witness or a global monochromaticity conclusion. -/
theorem exists_complete_source_relative_Q_transfer
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
        SourceRelativeTarget hb g final.toVariableWord O →
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
  exact sourceRelativeTarget_has_Q_preimage hb g f fallback O hO

/-- Source-level form: the actual ambient word, its full support, and
the source's syntactic refinement build the fibre frame canonically.
No separate ambient-bound or chosen-substitution hypothesis is needed. -/
theorem exists_complete_Q_transfer_of_source_refinement
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
        SourceRelativeTarget hb g final.toVariableWord O →
        ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput core fallback,
          w.1 ∈ f.span ∧
          observe (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            hb g fallback w) = observe O := by
  exact exists_complete_source_relative_Q_transfer hb
    (fibreFrameOfSyntactic core ambient hsupport hSource) f fallback hq

end DualTree.ForwardQFinalSyntacticSpanTransfer
