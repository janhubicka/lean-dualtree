import DualTree.QLengthNewIntrinsicHeight
import DualTree.SkewOrderObstruction
import DualTree.Lemma27QMarkerCoverage
import DualTree.Lemma27QOrderReduction

/-!
# A typed counterexample to the unrestricted reconstructed Q tree

The binary starred source, complete support and mixed-product element
are the exact source-facing objects in QLengthTypedWitness.
The two projected D₂ marker nodes are those in QLengthProjected,
not substitute or surrogate leaf labels.

Earlier modules establish the projected *ambient lengths* 2 and 1,
their membership in the actual reconstructed Q support, and their
equal intrinsic height 1 inside that support. The literal marker
prefixes show that the longer left node lexicographically precedes
the shorter right node. These facts directly violate clause (ii)
of the paper's executable skew definition.

This is a counterexample to the statement that the literal Q
tree construction, with arbitrary independent bullet coordinates
and the checked shortened safe local tail domain, always produces
a semi-complete skew support. It does not refute the final dual
Ramsey theorem, and does not yet decide whether synchronized-depth
bullet points or an alternate support order repair Lemma 27.
-/

namespace DualTree.QLengthActualSkewFailure

open QLengthTypedWitness

/-- The actual projected left D₂ marker extends the literal left
source signature marker 0. -/
theorem left_marker_prefix :
    IsPrefix ([0] : Node 2)
      (QLengthProjected.projection leftMarker).1 := by
  exact Lemma27QMarkerCoverage.marker_prefix_projected_point
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    cut_height_zero mixed leftMarker

/-- The actual projected right D₂ marker extends the literal
right source signature marker 1. -/
theorem right_marker_prefix :
    IsPrefix ([1] : Node 2)
      (QLengthProjected.projection rightMarker).1 := by
  exact Lemma27QMarkerCoverage.marker_prefix_projected_point
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    cut_height_zero mixed rightMarker

/-- Since the left and right Q projections begin with distinct
ambient letters 0 and 1, the left always precedes the right
lexicographically, regardless of the remaining tails. -/
theorem projected_left_lex_right :
    FinLexLE
      (QLengthProjected.projection leftMarker).1
      (QLengthProjected.projection rightMarker).1 := by
  obtain ⟨u, hu⟩ := left_marker_prefix
  obtain ⟨v, hv⟩ := right_marker_prefix
  rw [hu, hv]
  simp [FinLexLE, finLexLEB]

/-- The actual reconstructed Q node set violates the printed
skew clause (ii): its lexicographically earlier marker is
ambient-longer despite having the same intrinsic rank. -/
theorem sourceQ_condIIB_false :
    SkewTree.condIIB QLengthNewIntrinsicHeight.W.toList = false := by
  have hrank :
      SkewTree.heightAt QLengthNewIntrinsicHeight.W.toList
        (QLengthProjected.projection leftMarker).1 =
      SkewTree.heightAt QLengthNewIntrinsicHeight.W.toList
        (QLengthProjected.projection rightMarker).1 :=
    QLengthNewIntrinsicHeight.left_projection_Q_height_one.trans
      QLengthNewIntrinsicHeight.right_projection_Q_height_one.symm
  have hlength :
      (QLengthProjected.projection rightMarker).1.length <
      (QLengthProjected.projection leftMarker).1.length := by
    rw [QLengthProjected.left_projection_length_two,
      QLengthProjected.right_projection_length_one]
    omega
  exact SkewOrderObstruction.condIIB_false_of_rank_tie_length_reversal
    QLengthNewIntrinsicHeight.W.toList
    (QLengthProjected.projection leftMarker).1
    (QLengthProjected.projection rightMarker).1
    (QLengthNewIntrinsicHeight.projection_mem_Q leftMarker)
    (QLengthNewIntrinsicHeight.projection_mem_Q rightMarker)
    hrank projected_left_lex_right hlength

/-- The original Q tree is nonsingleton, hence failure of its
clause (ii) refutes the full printed skew predicate. -/
theorem sourceQ_skewB_false :
    SkewTree.skewB SkewTree.paperAuxB
      QLengthNewIntrinsicHeight.W.toList = false := by
  have hnon : QLengthNewIntrinsicHeight.W.toList.length ≠ 1 :=
    Lemma27QOrderReduction.sourceQ_nonsingleton
      (by decide : 0 < 2)
      source [] root_interior root_maximal exceptional_outside
      QLengthObstruction.completeT
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early
      cut_height_zero mixed
  exact SkewOrderObstruction.skewB_false_of_condIIB_false
    SkewTree.paperAuxB QLengthNewIntrinsicHeight.W.toList
    hnon sourceQ_condIIB_false

/-- The actual source-facing Q tree cannot be semi-complete
under the printed skew-tree order, independently of any
candidate word component g_w. -/
theorem sourceQ_semiCompleteB_false :
    SkewTree.semiCompleteB SkewTree.paperAuxB
      QLengthNewIntrinsicHeight.W.toList = false := by
  have hnon : QLengthNewIntrinsicHeight.W.toList.length ≠ 1 :=
    Lemma27QOrderReduction.sourceQ_nonsingleton
      (by decide : 0 < 2)
      source [] root_interior root_maximal exceptional_outside
      QLengthObstruction.completeT
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early
      cut_height_zero mixed
  exact SkewOrderObstruction.semiCompleteB_false_of_condIIB_false
    SkewTree.paperAuxB QLengthNewIntrinsicHeight.W.toList
    hnon sourceQ_condIIB_false

/-- Consequently no starred object can have this exact Q tree as
its underlying support: the tree alone violates semi-completeness. -/
theorem no_starred_Q_output :
    ¬ ∃ O' : StarredSignature.StarredWord
        2 3 1 Unit SkewTree.paperAuxB,
      O'.tree = QLengthNewIntrinsicHeight.W.toList := by
  rintro ⟨O', htree⟩
  have hsemi := O'.semi_complete
  rw [htree, sourceQ_semiCompleteB_false] at hsemi
  cases hsemi

end DualTree.QLengthActualSkewFailure
