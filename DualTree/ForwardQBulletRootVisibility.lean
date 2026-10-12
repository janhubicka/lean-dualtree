import DualTree.ForwardQRooted
import DualTree.ForwardQCanonicalConeRootChoice
import DualTree.ForwardQMarkerSmoothPartition

/-!
# Nonempty visible old-variable roots at every selected D2 frontier

The canonical source root is an ORIGINAL interior variable.
Every corrected literal R marker extends it, and every selected
D2 complete-support frontier extends that marker. The old source
root therefore strictly precedes every genuine D2 frontier
(the frontier is outside the inclusive final cut, while the
source root is inside it).

Hence the visible-old-root list at a D2 frontier is NEVER empty.
This removes the empty-cone obstruction to existence of a
root-aligned local cone-variable translation at the selected
D2 indices. Such an assertion is NOT made for all D0 frontiers.

As a concrete application, if genuine local cone variables occur
only in D2 coordinate cones (D0 local words are letters/auxiliary),
then there always exists a legal full-frontier three-way Q word
with the explicit source R_i decoder and a first-visible-root
cone-variable assignment.

This is not a proof that the assignment preserves independent
variable names, their Hales--Jewett span, or Definition 24's
simple-colouring witness. The canonical first-visible-root map
may identify names even when several are available.
-/

namespace DualTree.ForwardQBulletRootVisibility

open ForwardSourceQTree

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The true source root is an old source VARIABLE,
not merely an ambient T-support node. -/
noncomputable def sourceRootVariable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) : c.source.word.Vars :=
  Classical.choose
    (StarredSignature.variable_at_interior
      c.source (ForwardQRooted.sourceRoot c)
      (ForwardQRooted.sourceRoot_interior c))

/-- The chosen original source-variable root has exactly
the node supplied by the genuine rootedness certificate. -/
theorem sourceRootVariable_node
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    (sourceRootVariable c).1.1 = ForwardQRooted.sourceRoot c :=
  (Classical.choose_spec
    (StarredSignature.variable_at_interior
      c.source (ForwardQRooted.sourceRoot c)
      (ForwardQRooted.sourceRoot_interior c))).1

/-- The source root strictly precedes the literal corrected
signature-marker frontier of each REAL D2 bullet index. -/
theorem sourceRoot_strict_prefix_bullet_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (j : MixedProduct.BulletIndex (kind c)) :
    IsStrictPrefix (ForwardQRooted.sourceRoot c)
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 := by
  let r := ForwardQMeetClosed.markerOfBullet c j
  have hroot : IsPrefix (ForwardQRooted.sourceRoot c) r.1 :=
    ForwardQRooted.sourceRoot_prefix_literal_marker c r
  have hfront :
      IsPrefix r.1
        (ForwardOrderedProjections.frontierAt c.T c.cut
          (ForwardQMarkerCoverage.bulletForMarker c r).1).1 := by
    rw [ForwardQMarkerCoverage.bullet_frontier_eq_marker_frontier c r]
    exact (ForwardLiteralFrontierCoordinates.frontierFor_spec
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly r).2
  have hidx : ForwardQMarkerCoverage.bulletForMarker c r = j :=
    ForwardQMeetClosed.bulletForMarker_markerOfBullet c j
  have hpre : IsPrefix (ForwardQRooted.sourceRoot c)
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 := by
    have h := isPrefix_trans hroot hfront
    simpa only [hidx] using h
  have hbefore : ForwardAux (ForwardQRooted.sourceRoot c) c.cut := by
    have h := c.hmax
      (ForwardQRooted.sourceRoot c)
      (ForwardQRooted.sourceRoot_interior c)
    simpa only [SkewTree.forwardAuxB] using h
  have houtside :
      ¬ ForwardAux
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 c.cut :=
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1).2.1
  refine ⟨hpre, ?_⟩
  intro heq
  apply houtside
  rw [← heq]
  exact hbefore

/-- The SAME actual old source-variable name is visible at
every selected D2 frontier, regardless of its marked tail. -/
theorem sourceRootVariable_visible_bullet
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (j : MixedProduct.BulletIndex (kind c)) :
    (sourceRootVariable c).1.1 ∈
      ForwardQVisibleAncestorDecoder.visibleList c j.1 := by
  apply
    (ForwardQConeVariableVisibility.sourceRoot_visible_iff_strict_frontier
      c j.1 (sourceRootVariable c)).2
  rw [sourceRootVariable_node]
  exact sourceRoot_strict_prefix_bullet_frontier c j

/-- Every selected D2 frontier has at least one visible
old source-variable root. The D0 case is NOT included. -/
theorem bullet_visibleList_nonempty
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (j : MixedProduct.BulletIndex (kind c)) :
    0 < (ForwardQVisibleAncestorDecoder.visibleList c j.1).length := by
  have hv := sourceRootVariable_visible_bullet c j
  cases hs : ForwardQVisibleAncestorDecoder.visibleList c j.1 with
  | nil =>
      simp [hs] at hv
  | cons a rest =>
      simp [hs]

/-- Even the explicit m+1-symbol auxiliary decoder has
at least one label decoding to the genuine source-root
variable on EVERY selected D2 frontier. -/
theorem bullet_Ri_reaches_sourceRoot
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (j : MixedProduct.BulletIndex (kind c)) :
    ∃ a : Fin (m + 1),
      ForwardQVisibleAncestorDecoder.decodeAux c fallback j.1 a =
        Sum.inr (sourceRootVariable c) :=
  ForwardQVisibleRootCapacity.decodeAux_onto_every_visible_variable
    c fallback j.1 (sourceRootVariable c)
    (sourceRootVariable_visible_bullet c j)

/-- At every position of a selected D2 frontier cone,
the original source root is already an aligned variable. -/
theorem sourceRoot_aligned_in_bullet_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (j : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 t.1) :
    IsPrefix (sourceRootVariable c).1.1 t.1 := by
  have hstrict := sourceRoot_strict_prefix_bullet_frontier c j
  rw [sourceRootVariable_node]
  exact isPrefix_trans hstrict.1 ht

/-- When genuine local cone-variable occurrences are restricted
to selected D2 frontier coordinates, the exact nonempty-visible
condition is AUTOMATIC, even if D0 frontiers have no old roots. -/
theorem variables_only_bullet_implies_visible
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (hbullet : ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      kind c i = MixedProduct.CoordKind.bullet) :
    ForwardQCanonicalConeRootChoice.VariablesOnlyInVisibleCones c raw := by
  intro i t z ht hz
  let j : MixedProduct.BulletIndex (kind c) := ⟨i, hbullet i t z ht hz⟩
  exact bullet_visibleList_nonempty c j

/-- The existing concrete first-visible-root constructor therefore
produces a legal full-frontier three-way decoder for ANY raw local
words whose genuine variables appear only at D2 coordinates. -/
noncomputable def coneData_of_bullet_variables
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (hbullet : ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      kind c i = MixedProduct.CoordKind.bullet) :
    ForwardQFullFrontierThreeWay.ConeData c (Fin (m + 1)) κ :=
  ForwardQCanonicalConeRootChoice.coneData c fallback raw
    (variables_only_bullet_implies_visible c raw hbullet)

end DualTree.ForwardQBulletRootVisibility
