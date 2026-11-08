import DualTree.ForwardQFinalTargetNonemptyCore
import DualTree.ForwardQFinalTargetHeightBoundary

/-!
# Positive binary regression for the complete set-signature transfer

The concrete binary source, local word, and literal-target proof are built
independently in `ForwardQFinalTargetNonemptyCore`. This module checks the
same actual witness against the final set-signature interface and its
Q-preimage theorem.
-/

namespace DualTree.ForwardQFinalTargetNonemptyAudit

/-- The concrete positive target also belongs to the mathematical
set-signature class, independently of its list representation. -/
theorem binary_q2_sourceRelativeSetTarget :
    ForwardQFinalSetSpanTransfer.SourceRelativeSetTarget
      (by decide : 0 < 2) binaryFrame binaryFinalWord binarySource :=
  ForwardQFinalSetSpanTransfer.sourceRelativeSetTarget_of_literal
    binary_q2_sourceRelativeTarget

/-- The full finite-set-signature target class is genuinely inhabited
in the binary local-height-two instance. -/
theorem binary_q2_set_target_class_nonempty :
    {O : StarredSignature.StarredWord 2 3 1 Bool SkewTree.forwardAuxB |
      ForwardQFinalSetSpanTransfer.SourceRelativeSetTarget
        (by decide : 0 < 2) binaryFrame binaryFinalWord O}.Nonempty :=
  ⟨binarySource, binary_q2_sourceRelativeSetTarget⟩

/-- The set-signature transfer itself yields an actual starred Q
preimage for the positive binary example. -/
theorem binary_q2_has_actual_set_Q_preimage :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput binaryFrame.core false,
      w.1 ∈ binaryLocalWord.span ∧
      ForwardQFinalTargetObservation.observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            (by decide) binaryFrame false w) =
        ForwardQFinalTargetObservation.observe binarySource := by
  exact ForwardQFinalSetSpanTransfer.sourceRelativeSetTarget_has_Q_preimage
    (by decide) binaryFrame binaryLocalWord false binarySource
    binary_q2_sourceRelativeSetTarget

end DualTree.ForwardQFinalTargetNonemptyAudit
