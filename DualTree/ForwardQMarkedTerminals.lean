import DualTree.ForwardSourceQTree
import DualTree.Lemma27QTerminal

/-!
# Projected markers are terminal nodes in the corrected Q tree

The corrected Q support is the union of its fixed old base and
one projected node in each selected D₂ frontier cone. The sorted
frontiers are pairwise incomparable and lie outside the inclusive
forward-auxiliary cut. Every marked projection stays in its own
frontier cone and therefore also lies outside the cut.

Assume the retained old base lies inside the inclusive forward
cut. Then no marked projection can have an old-base descendant,
and no two different marked projections are comparable.
Consequently all newly projected points are genuine terminal
vertices of the Q support, and all its interior vertices belong
to the old base.

The remaining source-specific requirement is to prove the
old-base cut hypothesis from the exact corrected signature
interior identity. That identity is a separate Lean proof,
ForwardSignatureInteriorExact; here it remains an explicit
hypothesis, not a disguised imported axiom.
-/

namespace DualTree.ForwardQMarkedTerminals

open ForwardSourceQTree

/-- The minimal complete-support frontier beyond the inclusive
forward cut stays outside that cut after canonical projection. -/
theorem markedProjection_outside_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    ¬ ForwardAux (markedProjection c x i).1 c.cut := by
  have hfront :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1
  exact ForwardInclusiveFrontier.outside_of_prefix
    hfront.2.1 (markedProjection_cone c x i)

/-- If the fixed base is at/before the cut, no newly projected
point has any strict descendant anywhere in the corrected Q
support (not even among the other projected points). -/
theorem markedProjection_no_strict_descendant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hbase : ∀ s, s ∈ oldBase c → ForwardAux s c.cut)
    (i : MixedProduct.BulletIndex (kind c))
    (s : Node b)
    (hs : s ∈ nodes c x) :
    ¬ IsStrictPrefix (markedProjection c x i).1 s := by
  classical
  intro hstrict
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun j => (markedProjection c x j).1) at hs
  rcases Finset.mem_union.mp hs with hold | hnew
  · have hearly : ForwardAux s c.cut :=
      hbase s (List.mem_toFinset.mp hold)
    exact (markedProjection_outside_cut c x i)
      (ForwardInclusiveFrontier.forwardAux_of_prefix
        hstrict.1 hearly)
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hnew
    have hpj : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1
        s := by
      rw [← hj]
      exact markedProjection_cone c x j
    have hfi :=
      ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1
    have hfj :=
      ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1
    have hpi : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1
        s :=
      isPrefix_trans (markedProjection_cone c x i) hstrict.1
    have hfEq :
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 :=
      CutFrontier.frontier_unique_above
        c.T (fun u => ForwardAux u c.cut)
        hfi hfj hpi hpj
    have hindex : i.1 = j.1 :=
      ForwardOrderedProjections.frontierAt_injective c.T c.cut
        (Subtype.ext hfEq)
    have hij : i = j := Subtype.ext hindex
    subst j
    have his : (markedProjection c x i).1 = s := hj
    exact hstrict.2 his

/-- Every newly projected D₂ point is actually a leaf of the
corrected Q support. -/
theorem markedProjection_not_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hbase : ∀ s, s ∈ oldBase c → ForwardAux s c.cut)
    (i : MixedProduct.BulletIndex (kind c)) :
    (markedProjection c x i).1 ∉
      SkewTree.interior (nodes c x).toList := by
  exact Lemma27QTerminal.not_interior_of_no_strict_descendant
    (nodes c x).toList (markedProjection c x i).1
    (fun s hs =>
      markedProjection_no_strict_descendant
        c x hbase i s (Finset.mem_toList.mp hs))

/-- Under the base-cut hypothesis, all Q interior vertices are
old base vertices. No new D₂ root is accidentally interior. -/
theorem interior_subset_oldBase
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hbase : ∀ s, s ∈ oldBase c → ForwardAux s c.cut)
    (s : Node b)
    (hs : s ∈ SkewTree.interior (nodes c x).toList) :
    s ∈ oldBase c := by
  classical
  have hsW : s ∈ nodes c x :=
    Finset.mem_toList.mp (List.mem_filter.mp hs).1
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun j => (markedProjection c x j).1) at hsW
  rcases Finset.mem_union.mp hsW with hold | hnew
  · exact List.mem_toFinset.mp hold
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hnew
    rw [← hi] at hs
    exact False.elim
      ((markedProjection_not_interior c x hbase i) hs)

end DualTree.ForwardQMarkedTerminals
