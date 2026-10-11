import DualTree.ForwardQMarkedTerminals
import DualTree.ForwardQSourceTerminals

/-!
# Pairwise disjoint marked Q cones avoiding all old source variable roots

The corrected Q support is formed by retaining the old source
interior and projecting one point into each selected D₂ frontier
cone. A later mixed-cone word construction must be able to
replace values in the *inclusive* cones above these points.

Here we verify the two geometric conditions needed for
unambiguous patching:

1. No old source variable root lies in a projected-point cone.
   Each source root is an interior vertex at or before the final
   forward cut, whereas every projected point is outside that
   inclusive forward cut.
2. Two distinct selected projected-point cones have no common
   ambient extension, even among nodes outside the support T.
   They belong to different minimal outside-cut T frontiers,
   and those frontiers form a prefix antichain.

These facts require no D₂ point-length ordering, colouring,
or source-domain certificate. The resulting disjointness
is useful for constructing a word g_w by independent patches
inside the marked D₂ cones while preserving root symbols.
It does NOT itself prove the resulting word is valid or
that any colouring pullback is smooth.
-/

namespace DualTree.ForwardQDisjointWordCones

open ForwardSourceQTree

/-- Every marked projection lies outside the forward-inclusive
cut, and hence cannot be an ambient prefix of any original
source variable root. -/
theorem projected_cone_avoids_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c))
    (v : c.source.word.Vars) :
    ¬ IsPrefix (markedProjection c x i).1 v.1.1 := by
  intro hpre
  have hvInterior : v.1.1 ∈ SkewTree.interior c.source.tree :=
    StarredSignature.variable_root_in_interior c.source v
  have hvBefore : ForwardAux v.1.1 c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax v.1.1 hvInterior
  have hProjBefore : ForwardAux (markedProjection c x i).1 c.cut :=
    ForwardInclusiveFrontier.forwardAux_of_prefix hpre hvBefore
  exact (ForwardQMarkedTerminals.markedProjection_outside_cut
    c x i) hProjBefore

/-- Two distinct marked projected-point cones share no ambient
extension. This is stronger than injectivity of the projected
points, and does not assume the common extension lies in T. -/
theorem projected_cones_no_common_extension
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i ≠ j)
    (t : Node b) :
    ¬ (IsPrefix (markedProjection c x i).1 t ∧
       IsPrefix (markedProjection c x j).1 t) := by
  intro ⟨hi, hj⟩
  have hfi :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1
  have hfj :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1
  have hFronti : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 t :=
    isPrefix_trans (markedProjection_cone c x i) hi
  have hFrontj : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 t :=
    isPrefix_trans (markedProjection_cone c x j) hj
  have hFrontEq :
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 :=
    CutFrontier.frontier_unique_above c.T
      (fun u => ForwardAux u c.cut) hfi hfj hFronti hFrontj
  have hindex : i.1 = j.1 :=
    ForwardOrderedProjections.frontierAt_injective
      c.T c.cut (Subtype.ext hFrontEq)
  exact hij (Subtype.ext hindex)

/-- The actual projected Q points from distinct selected D₂
coordinates are prefix-incomparable in both directions. -/
theorem projected_nodes_incomparable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i ≠ j) :
    ¬ IsPrefix (markedProjection c x i).1
        (markedProjection c x j).1 ∧
    ¬ IsPrefix (markedProjection c x j).1
        (markedProjection c x i).1 := by
  constructor
  · intro h
    exact projected_cones_no_common_extension c x i j hij
      (markedProjection c x j).1
      ⟨h, isPrefix_refl _⟩
  · intro h
    exact projected_cones_no_common_extension c x i j hij
      (markedProjection c x i).1
      ⟨isPrefix_refl _, h⟩

end DualTree.ForwardQDisjointWordCones
