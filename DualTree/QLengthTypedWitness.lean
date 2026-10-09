import DualTree.QLengthObstruction
import DualTree.Lemma27QMarkerCount
import DualTree.LocalMixedElementFromMarkers
import DualTree.Lemma27QMarkerCoverage

/-!
# A literal starred source and independently chosen bullet depths

We construct a genuinely typed instance of the original Lemma 27
hypotheses with b=2, ambient height 3, one starred interior node and a
3-complete binary ambient skew support.  The independently selected
left and right literal signature markers receive local tails of
length one and zero, respectively.

This verifies that the *mixed-product interface* admits independent
marked depths. It does not yet prove which precise ambient nodes are
obtained after the canonical cone projections, nor that the final
sourceSignatureNodes set violates a skew order clause.
-/

namespace DualTree.QLengthTypedWitness

/-- The bounded root of the 3-level binary homogeneous tree. -/
def rootBounded : BoundedNode 2 3 := ⟨[], by simp [InHomTree]⟩

/-- A variable word with exactly one variable, occurring
at every node and rooted at the empty word. -/
noncomputable def rootVariable : VariableWord 2 3 Unit where
  support := [rootBounded]
  support_nodup := by simp
  word := fun _ => Sum.inr ⟨rootBounded, by simp⟩
  atRoot := by
    intro v
    have hv : v.1 = rootBounded := by simpa using v.2
    cases v with
    | mk t ht =>
        dsimp at hv
        subst t
        rfl
  below := by
    intro v i _
    have hv : v.1 = rootBounded := by simpa using v.2
    rw [hv]
    exact ⟨i.1, by simp [rootBounded]⟩

/-- A literal starred object based on S={empty,0,1}. -/
noncomputable def source :
    StarredSignature.StarredWord 2 3 1 Unit SkewTree.paperAuxB where
  tree := QLengthObstruction.originalS
  tree_bounded := by
    intro t ht
    have hcases : t = [] ∨ t = [0] ∨ t = [1] := by
      simpa [QLengthObstruction.originalS] using ht
    rcases hcases with h | h | h <;> subst t <;> simp [InHomTree]
  semi_complete := QLengthObstruction.originalS_is_semiComplete
  word := rootVariable
  interior_card := by decide
  support_eq_interior := by
    intro t
    have hI : SkewTree.interior QLengthObstruction.originalS =
        ([[]] : List (Node 2)) := by decide
    simp [VariableWord.supportNodes, rootVariable, rootBounded, hI]
  support_skew := by
    intro _
    change SkewTree.skewB SkewTree.paperAuxB
      ([[]] : List (Node 2)) = true
    exact SkewTree.singleton_skewB SkewTree.paperAuxB []

/-- The distinguished maximal interior cut is the empty word. -/
theorem root_interior :
    ([] : Node 2) ∈ SkewTree.interior source.tree := by
  decide

theorem root_maximal :
    ∀ t, t ∈ SkewTree.interior source.tree →
      SkewTree.paperAuxB t [] = true := by
  intro t ht
  have hI : SkewTree.interior source.tree =
      ([[]] : List (Node 2)) := by decide
  have hteq : t = [] := by simpa [hI] using ht
  subst t
  decide

/-- Every source node belongs to the ambient complete skew support. -/
theorem source_subset_complete :
    ∀ t, t ∈ source.tree → t ∈ QLengthObstruction.completeT := by
  intro t ht
  have hcases : t = [] ∨ t = [0] ∨ t = [1] := by
    simpa [source, QLengthObstruction.originalS] using ht
  rcases hcases with h | h | h <;> subst t <;>
    simp [QLengthObstruction.completeT]

theorem cut_in_complete :
    ([] : Node 2) ∈ QLengthObstruction.completeT := by
  simp [QLengthObstruction.completeT]

theorem cut_level_early :
    SkewTree.heightAt QLengthObstruction.completeT ([] : Node 2) + 1 < 3 := by
  decide

theorem cut_height_zero :
    SkewTree.heightAt QLengthObstruction.completeT ([] : Node 2) = 0 := by
  decide

/-- No exceptional source leaf lies before the root cut: indeed,
the root is a prefix of every ambient node. -/
theorem exceptional_outside :
    ∀ t, t ∈ StarredSignature.exceptionalLeaves source ([] : Node 2) →
      ¬ SignatureBoundary.BeforeCut [] t := by
  intro t ht
  have hnot : ¬ IsPrefix ([] : Node 2) t :=
    (StarredSignature.exceptionalLeaves_spec source [] t ht).2.2
  exact False.elim (hnot ⟨t, by simp⟩)

/-- The left and right children are genuinely in the literal marker set R. -/
theorem left_mem_R :
    ([0] : Node 2) ∈
      LiteralSignatureR.literalR source [] exceptional_outside := by
  simpa using
    (Lemma27QMarkerCoverage.child_mem_literalR
      source [] exceptional_outside (0 : Fin 2))

theorem right_mem_R :
    ([1] : Node 2) ∈
      LiteralSignatureR.literalR source [] exceptional_outside := by
  simpa using
    (Lemma27QMarkerCoverage.child_mem_literalR
      source [] exceptional_outside (1 : Fin 2))

def leftMarker :
    {s : Node 2 //
      s ∈ LiteralSignatureR.literalR source [] exceptional_outside} :=
  ⟨[0], left_mem_R⟩

def rightMarker :
    {s : Node 2 //
      s ∈ LiteralSignatureR.literalR source [] exceptional_outside} :=
  ⟨[1], right_mem_R⟩

/-- Choose a one-letter local tail at the left marked coordinate
and the empty local tail at the right marked coordinate. -/
noncomputable def chosenPoint
    (s : {s : Node 2 //
      s ∈ LiteralSignatureR.literalR source [] exceptional_outside}) :
    BoundedNode 2 (3 - (0 + 1)) :=
  if s.1 = [0] then ⟨[0], by simp [InHomTree]⟩ else ⟨[], by simp [InHomTree]⟩

theorem chosenPoint_left_length :
    (chosenPoint leftMarker).1.length = 1 := by
  simp [chosenPoint, leftMarker]

theorem chosenPoint_right_length :
    (chosenPoint rightMarker).1.length = 0 := by
  simp [chosenPoint, rightMarker]

/-- Construct the actual typed source mixed-product element,
with no up slots and designated bullet points for R. -/
noncomputable def mixed :
    MixedProduct.Element 2 (3 - (0 + 1))
      (LiteralFrontierCount.frontiers QLengthObstruction.completeT
        ([] : Node 2)).length Unit
      (LiteralMarkerProductKind.kind
        source [] root_interior root_maximal exceptional_outside
        QLengthObstruction.completeT
        QLengthObstruction.completeT_is_complete
        source_subset_complete cut_in_complete cut_level_early) :=
  LocalMixedElementFromMarkers.assemble
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    (fun _ _ => ()) chosenPoint

/-- Exact source-facing bullet coordinate lookup, not just
some arbitrary list of two points. -/
theorem left_bullet_is_chosen :
    mixed.bulletPoint
      (MixedProduct.bulletIndex
        (LiteralMarkerCoordinates.coordinate
          source [] root_interior root_maximal exceptional_outside
          QLengthObstruction.completeT
          QLengthObstruction.completeT_is_complete
          source_subset_complete cut_in_complete cut_level_early)
        leftMarker) = chosenPoint leftMarker := by
  exact LocalMixedElementFromMarkers.assemble_marker_point
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    (fun _ _ => ()) chosenPoint leftMarker

theorem right_bullet_is_chosen :
    mixed.bulletPoint
      (MixedProduct.bulletIndex
        (LiteralMarkerCoordinates.coordinate
          source [] root_interior root_maximal exceptional_outside
          QLengthObstruction.completeT
          QLengthObstruction.completeT_is_complete
          source_subset_complete cut_in_complete cut_level_early)
        rightMarker) = chosenPoint rightMarker := by
  exact LocalMixedElementFromMarkers.assemble_marker_point
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    (fun _ _ => ()) chosenPoint rightMarker

end DualTree.QLengthTypedWitness
