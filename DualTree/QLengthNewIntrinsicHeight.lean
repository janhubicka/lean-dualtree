import DualTree.QLengthProjected
import DualTree.Lemma27QInterior

/-!
# Intrinsic height of projected leaves when Q has one interior

A support can be non-prefix-closed, so ambient word length
does not compute its intrinsic height. This file proves the
required *support-internal* rank argument separately.

In any duplicate-free finite support whose only interior vertex
is the root [], each nonroot vertex has exactly one strict
support predecessor, namely []. Thus its intrinsic height is one.

We instantiate this with the exact reconstructed Q support of
the typed binary source and both true canonical marker projections.
No conclusion about skewness is made without also checking their
lexicographic order and unequal ambient depths.
-/

namespace DualTree.QLengthNewIntrinsicHeight

open QLengthTypedWitness

/-- In a finite duplicate-free support whose only non-leaf
is the empty root, every other support vertex has intrinsic
height exactly one. -/
theorem nonroot_height_one_of_single_interior
    {b : Nat} (S : List (Node b))
    (hnodup : S.Nodup)
    (hroot : ([] : Node b) ∈ S)
    (hinterior : ∀ u : Node b, u ∈ SkewTree.interior S → u = [])
    (x : Node b) (hx : x ∈ S) (hxne : x ≠ []) :
    SkewTree.heightAt S x = 1 := by
  have hrootStrict : IsStrictPrefix ([] : Node b) x := by
    refine ⟨⟨x, by simp⟩, ?_⟩
    exact Ne.symm hxne
  have hrootPred : ([] : Node b) ∈ SkewTree.preds S x := by
    change ([] : Node b) ∈
      S.filter (fun u => SkewTree.strictPrefixB u x)
    exact List.mem_filter.mpr
      ⟨hroot, (SkewBranchGeometry.strictPrefixB_iff [] x).2 hrootStrict⟩
  have hpredOnly :
      ∀ u : Node b, u ∈ SkewTree.preds S x → u = [] := by
    intro u hu
    have hp : u ∈ S.filter
        (fun y => SkewTree.strictPrefixB y x) := hu
    obtain ⟨huS, huB⟩ := List.mem_filter.mp hp
    have huStrict : IsStrictPrefix u x :=
      (SkewBranchGeometry.strictPrefixB_iff u x).1 huB
    have huInterior : u ∈ SkewTree.interior S :=
      SignatureInteriorPersistence.interior_of_strict_descendant
        S u x huS hx huStrict
    exact hinterior u huInterior
  have hpredNoDup : (SkewTree.preds S x).Nodup := by
    unfold SkewTree.preds
    exact hnodup.filter _
  have hpredFin :
      (SkewTree.preds S x).toFinset = {([] : Node b)} := by
    classical
    ext u
    simp only [List.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact hpredOnly u
    · intro heq
      subst u
      exact hrootPred
  have hcard := List.toFinset_card_of_nodup hpredNoDup
  rw [hpredFin] at hcard
  have hlen : (SkewTree.preds S x).length = 1 := by
    simp at hcard
    omega
  exact hlen

/-- The actual Q node set for the typed binary source. -/
noncomputable def W : Finset (Node 2) :=
  Lemma27SignatureTree.sourceSignatureNodes
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    cut_height_zero mixed

/-- The original root remains a node of the reconstructed Q support. -/
theorem root_mem_Q : ([] : Node 2) ∈ W.toList := by
  exact Lemma27QInterior.originalInterior_mem_Q
    source [] root_interior root_maximal exceptional_outside
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    source_subset_complete cut_in_complete cut_level_early
    cut_height_zero mixed ([] : Node 2) root_interior

/-- Every interior vertex of the actual Q support is its
retained original root, independent of the chosen marker depths. -/
theorem Q_interior_eq_root
    (u : Node 2) (hu : u ∈ SkewTree.interior W.toList) :
    u = [] := by
  have huOld : u ∈ SkewTree.interior source.tree :=
    (Lemma27QInterior.source_interior_iff_original
      (by decide : 0 < 2)
      source [] root_interior root_maximal exceptional_outside
      QLengthObstruction.completeT
      QLengthObstruction.completeT_is_complete
      source_subset_complete cut_in_complete cut_level_early
      cut_height_zero mixed u).1 hu
  have hI : SkewTree.interior source.tree =
      ([[]] : List (Node 2)) := by decide
  simpa only [hI, List.mem_singleton] using huOld

/-- The literal projected point at a D₂ marker is genuinely
a member of the source-facing Q node set. -/
theorem projection_mem_Q (s : QLengthProjected.Marker) :
    (QLengthProjected.projection s).1 ∈ W.toList := by
  have hp := Lemma27SignatureTree.signatureNodes_marked
    QLengthObstruction.completeT
    QLengthObstruction.completeT_is_complete
    ([] : Node 2) cut_in_complete cut_level_early
    cut_height_zero
    (Lemma27SignatureTree.oldSignatureBase
      source [] exceptional_outside)
    mixed (QLengthProjected.index s)
  apply Finset.mem_toList.mpr
  simpa only [W, QLengthProjected.projection,
    Lemma27SignatureTree.sourceSignatureNodes] using hp

/-- Any nonroot projected Q node has intrinsic height one. -/
theorem nonroot_Q_height_one
    (s : Node 2) (hs : s ∈ W.toList) (hne : s ≠ []) :
    SkewTree.heightAt W.toList s = 1 := by
  exact nonroot_height_one_of_single_interior
    W.toList (Finset.nodup_toList W)
    root_mem_Q Q_interior_eq_root s hs hne

/-- The left projected marker has intrinsic height one in the
*new* Q support, despite ambient word length two. -/
theorem left_projection_Q_height_one :
    SkewTree.heightAt W.toList
      (QLengthProjected.projection leftMarker).1 = 1 := by
  have hne : (QLengthProjected.projection leftMarker).1 ≠ [] := by
    intro h
    have hh := QLengthProjected.left_projection_length_two
    rw [h] at hh
    simp at hh
  exact nonroot_Q_height_one _
    (projection_mem_Q leftMarker) hne

/-- The right projected marker also has intrinsic height one
in the new Q support, with ambient word length one. -/
theorem right_projection_Q_height_one :
    SkewTree.heightAt W.toList
      (QLengthProjected.projection rightMarker).1 = 1 := by
  have hne : (QLengthProjected.projection rightMarker).1 ≠ [] := by
    intro h
    have hh := QLengthProjected.right_projection_length_one
    rw [h] at hh
    simp at hh
  exact nonroot_Q_height_one _
    (projection_mem_Q rightMarker) hne

end DualTree.QLengthNewIntrinsicHeight
