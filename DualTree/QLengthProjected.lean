import DualTree.QLengthTypedWitness
import DualTree.UniformConeDomains

/-!
# Actual projected ambient depths in the typed Lemma 27 Q witness

We no longer examine an analogous leaf-replacement set. We use the
literal Q source and its actual two D₂ coordinates from
QLengthTypedWitness, including its canonical frontier choices and
intrinsic safe cone projections.

The complete ambient support is the homogeneous binary tree of
height three, where intrinsic rank equals ambient word length.
For the root cut, each marker is itself the minimal support frontier
outside the cut. The true Q projections therefore have ambient
length two on the left and length one on the right.

This still does not identify the new support's *intrinsic*
heights, so a separate theorem must check condition (ii) on the
actual Q support before claiming a source-facing counterexample.
-/

namespace DualTree.QLengthProjected

open QLengthTypedWitness

abbrev T : List (Node 2) := QLengthObstruction.completeT

abbrev Marker :=
  {s : Node 2 //
    s ∈ LiteralSignatureR.literalR source [] exceptional_outside}

/-- Each concrete ambient node in the full binary support has
intrinsic height exactly equal to its ambient word length. -/
theorem full_support_rank_eq_length
    (t : Node 2) (ht : t ∈ T) :
    SkewTree.heightAt T t = t.length := by
  simp [T, QLengthObstruction.completeT] at ht
  rcases ht with h | h | h | h | h | h | h <;>
    subst t <;> decide

/-- For a marker already in the ambient complete support and
outside the inclusive cut, its unique assigned minimal outside-cut
frontier must be that marker itself. -/
theorem frontierFor_eq_marker
    (s : Marker)
    (hmem : s.1 ∈ T) (hout : ¬ PaperAux s.1 []) :
    LiteralFrontierIndex.frontierFor
      source [] root_interior root_maximal exceptional_outside T
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early s = s.1 := by
  have hspec := LiteralFrontierIndex.frontierFor_spec
    source [] root_interior root_maximal exceptional_outside T
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early s
  by_contra hneq
  exact hout (hspec.1.2.2 s.1 hmem ⟨hspec.2, Ne.symm hneq⟩)

/-- The actual literal left marker's assigned frontier is [0]. -/
theorem left_frontier_eq :
    LiteralFrontierIndex.frontierFor
      source [] root_interior root_maximal exceptional_outside T
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early leftMarker =
      ([0] : Node 2) := by
  have hmem : leftMarker.1 ∈ T := by
    change ([0] : Node 2) ∈ T
    decide
  have hout : ¬ PaperAux leftMarker.1 [] := by
    change ¬ PaperAux ([0] : Node 2) []
    decide
  exact frontierFor_eq_marker leftMarker hmem hout

/-- The actual literal right marker's assigned frontier is [1]. -/
theorem right_frontier_eq :
    LiteralFrontierIndex.frontierFor
      source [] root_interior root_maximal exceptional_outside T
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early rightMarker =
      ([1] : Node 2) := by
  have hmem : rightMarker.1 ∈ T := by
    change ([1] : Node 2) ∈ T
    decide
  have hout : ¬ PaperAux rightMarker.1 [] := by
    change ¬ PaperAux ([1] : Node 2) []
    decide
  exact frontierFor_eq_marker rightMarker hmem hout

/-- The true D₂ index of a literal marker. -/
noncomputable def index (s : Marker) :
    MixedProduct.BulletIndex
      (LiteralMarkerProductKind.kind
        source [] root_interior root_maximal exceptional_outside T
        QLengthObstruction.completeT_is_complete
        source_subset_complete cut_in_complete cut_level_early) :=
  MixedProduct.bulletIndex
    (LiteralMarkerCoordinates.coordinate
      source [] root_interior root_maximal exceptional_outside T
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early) s

/-- The exact support-valued projected node used in the literal Q map. -/
noncomputable def projection (s : Marker) : {t : Node 2 // t ∈ T} :=
  Lemma27SignatureTree.markedProjection
    T QLengthObstruction.completeT_is_complete
    ([] : Node 2) cut_in_complete cut_level_early cut_height_zero
    mixed (index s)

/-- The assigned index retrieves the marker's frontier
through the literal frontier enumeration. -/
theorem indexed_frontier_eq
    (s : Marker)
    (hmem : s.1 ∈ T) (hout : ¬ PaperAux s.1 []) :
    (Lemma27SignatureTree.frontierAt T [] (index s).1).1 = s.1 := by
  have hcoord := LiteralMarkerCoordinates.coordinate_frontier
    source [] root_interior root_maximal exceptional_outside T
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early s
  change
    (Lemma27SignatureTree.frontierAt T [] (index s).1).1 =
      LiteralFrontierIndex.frontierFor
        source [] root_interior root_maximal exceptional_outside T
        QLengthObstruction.completeT_is_complete
        source_subset_complete cut_in_complete cut_level_early s
      at hcoord
  exact hcoord.trans (frontierFor_eq_marker s hmem hout)

/-- Local tail length adds exactly to the intrinsic rank of the
original ambient support under the true Q marked projection. -/
theorem projection_rank (s : Marker) :
    SkewTree.heightAt T (projection s).1 =
      SkewTree.heightAt T
        (Lemma27SignatureTree.frontierAt T [] (index s).1).1 +
      (mixed.bulletPoint (index s)).1.length := by
  exact UniformConeDomains.projectCommon_height
    T QLengthObstruction.completeT_is_complete
    ([] : Node 2) cut_in_complete cut_level_early cut_height_zero
    (Lemma27SignatureTree.frontierAt T [] (index s).1)
    (Lemma27SignatureTree.frontierAt_spec T [] (index s).1)
    (mixed.bulletPoint (index s))

/-- The actual left projected point occupies ambient level two. -/
theorem left_projection_length_two :
    (projection leftMarker).1.length = 2 := by
  have hmem : leftMarker.1 ∈ T := by
    change ([0] : Node 2) ∈ T
    decide
  have hout : ¬ PaperAux leftMarker.1 [] := by
    change ¬ PaperAux ([0] : Node 2) []
    decide
  have hfr : (Lemma27SignatureTree.frontierAt
      T [] (index leftMarker).1).1 = ([0] : Node 2) :=
    indexed_frontier_eq leftMarker hmem hout
  have hfrRank : SkewTree.heightAt T
      (Lemma27SignatureTree.frontierAt T [] (index leftMarker).1).1 = 1 := by
    rw [hfr]
    decide
  have hbullet : (mixed.bulletPoint (index leftMarker)).1.length = 1 := by
    have h := congrArg
      (fun z : BoundedNode 2 (3 - (0 + 1)) => z.1.length)
      left_bullet_is_chosen
    exact h.trans chosenPoint_left_length
  have hrank := projection_rank leftMarker
  have hfull := full_support_rank_eq_length
    (projection leftMarker).1 (projection leftMarker).2
  omega

/-- The actual right projected point occupies ambient level one. -/
theorem right_projection_length_one :
    (projection rightMarker).1.length = 1 := by
  have hmem : rightMarker.1 ∈ T := by
    change ([1] : Node 2) ∈ T
    decide
  have hout : ¬ PaperAux rightMarker.1 [] := by
    change ¬ PaperAux ([1] : Node 2) []
    decide
  have hfr : (Lemma27SignatureTree.frontierAt
      T [] (index rightMarker).1).1 = ([1] : Node 2) :=
    indexed_frontier_eq rightMarker hmem hout
  have hfrRank : SkewTree.heightAt T
      (Lemma27SignatureTree.frontierAt T [] (index rightMarker).1).1 = 1 := by
    rw [hfr]
    decide
  have hbullet : (mixed.bulletPoint (index rightMarker)).1.length = 0 := by
    have h := congrArg
      (fun z : BoundedNode 2 (3 - (0 + 1)) => z.1.length)
      right_bullet_is_chosen
    exact h.trans chosenPoint_right_length
  have hrank := projection_rank rightMarker
  have hfull := full_support_rank_eq_length
    (projection rightMarker).1 (projection rightMarker).2
  omega

end DualTree.QLengthProjected
