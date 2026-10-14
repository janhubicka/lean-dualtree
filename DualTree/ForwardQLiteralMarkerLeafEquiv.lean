import DualTree.ForwardQInteriorExact
import DualTree.ForwardQSourceTerminals
import DualTree.ForwardQMarkerCoverage

/-!
# The literal corrected R markers are EXACTLY the Q terminal vertices

For the genuine globally forward-corrected Lemma 27 Q construction,
the Q support is the original source interior together with precisely
one projected terminal node for each selected D2 coordinate.
Previous modules separately proved its exact interior and the fact
that every marked projection is terminal.

This module proves the missing CONVERSE: every Q terminal node must
be a selected D2 marked projection. The retained old signature base
equals the original source interior and therefore cannot contribute a
terminal node to Q. Together with the established injectivity of
different projected frontiers, this constructs canonical equivalences

    BulletIndex(kind c) ≃ Leaves(Q(c,x)),
    LiteralR(c) ≃ Leaves(Q(c,x)).

The R-to-leaf equivalence depends on the actual starred input only
through its projected terminal points; the R-to-D2 coordinate bijection
itself depends only on the fixed corrected source frame.

This is not yet the paper's abstract canonical model-boundary
identification A ≃ R. It isolates that remaining task from the
previously conditional simplicity-to-smoothness theorem and proves
that there are NO unaccounted-for Q leaves.
-/

namespace DualTree.ForwardQLiteralMarkerLeafEquiv

open ForwardSourceQTree

/-- Actual terminal vertices of the corrected Q support,
with proof that they belong to Q and are not interior. -/
abbrev QLeaf
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :=
  {s : Node b //
    s ∈ (nodes c x).toList ∧
    s ∉ SkewTree.interior (nodes c x).toList}

/-- Every selected D2 coordinate gives a genuine Q terminal. -/
noncomputable def bulletToQLeaf
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c)) :
    QLeaf c x :=
  ⟨(markedProjection c x j).1,
    ⟨Finset.mem_toList.mpr (markedProjection_mem c x j),
      ForwardQSourceTerminals.markedProjection_terminal c x j⟩⟩

/-- The terminal part of Q consists of marked D2 projections only.
There are no leftover old-base/source-interior terminal nodes. -/
theorem Q_leaf_has_bullet
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (leaf : QLeaf c x) :
    ∃ j : MixedProduct.BulletIndex (kind c),
      (markedProjection c x j).1 = leaf.1 := by
  classical
  have hnode : leaf.1 ∈ nodes c x :=
    Finset.mem_toList.mp leaf.2.1
  change leaf.1 ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hnode
  rcases Finset.mem_union.mp hnode with hold | hmark
  · have hbase : leaf.1 ∈ oldBase c :=
      List.mem_toFinset.mp hold
    have horiginal : leaf.1 ∈ SkewTree.interior c.source.tree :=
      (ForwardQFixedBase.oldBase_mem_iff_original_interior
        c leaf.1).1 hbase
    have hQinterior :
        leaf.1 ∈ SkewTree.interior (nodes c x).toList :=
      (ForwardQInteriorExact.Q_interior_iff_original
        hb c x leaf.1).2 horiginal
    exact False.elim (leaf.2.2 hQinterior)
  · obtain ⟨j, _, hprojection⟩ := Finset.mem_image.mp hmark
    exact ⟨j, hprojection⟩

/-- The bullet-to-leaf map is injective: distinct corrected
frontier cones contain distinct projected terminal nodes. -/
theorem bulletToQLeaf_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    Function.Injective (bulletToQLeaf c x) := by
  intro i j hij
  have hnodes :
      (markedProjection c x i).1 =
        (markedProjection c x j).1 :=
    congrArg (fun leaf : QLeaf c x => leaf.1) hij
  exact (markedProjection_injective c x)
    (Subtype.ext hnodes)

/-- Every Q terminal is obtained from some actual D2 index. -/
theorem bulletToQLeaf_surjective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    Function.Surjective (bulletToQLeaf c x) := by
  intro leaf
  obtain ⟨j, hj⟩ := Q_leaf_has_bullet hb c x leaf
  exact ⟨j, Subtype.ext hj⟩

/-- The genuine corrected D2 coordinate type is in canonical
bijection with the terminal vertices of the actual Q tree. -/
noncomputable def bulletQLeafEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    MixedProduct.BulletIndex (kind c) ≃ QLeaf c x :=
  Equiv.ofBijective (bulletToQLeaf c x)
    ⟨bulletToQLeaf_injective c x,
      bulletToQLeaf_surjective hb c x⟩

/-- The first half of the canonical boundary correspondence:
the literal corrected R marker set and actual selected
D2 coordinates have a bijection determined by the fixed frame. -/
noncomputable def literalMarkerBulletEquiv
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout ≃
        MixedProduct.BulletIndex (kind c) :=
  Equiv.ofBijective (ForwardQMarkerCoverage.bulletForMarker c)
    (ForwardSortedMixedProduct.bulletIndex_bijective
      c.source c.cut c.hcut c.hmax c.hout c.T
      c.hcomplete c.hnon c.hST c.hcutT c.hearly)

/-- Exact source-facing endpoint:
every literal corrected signature marker r corresponds to
one Q terminal P_(index r)(s_index r), and EVERY Q terminal
comes from a unique literal marker r. -/
noncomputable def literalMarkerQLeafEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    ForwardSortedMixedProduct.Marker c.source c.cut c.hout ≃
      QLeaf c x :=
  (literalMarkerBulletEquiv c).trans (bulletQLeafEquiv hb c x)

/-- The equivalence uses the ORIGINAL projected point formula,
not an artificial relabeling of Q terminal nodes. -/
theorem literalMarkerQLeafEquiv_value
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker c.source c.cut c.hout) :
    ((literalMarkerQLeafEquiv hb c x) r).1 =
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c r)).1 :=
  rfl

/-- A terminal Q node and its unique literal R marker are in
the same forward minimal-support frontier cone, as witnessed
by the actual marker-to-projection prefix lemma. -/
theorem marker_prefix_its_Q_leaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker c.source c.cut c.hout) :
    IsPrefix r.1 ((literalMarkerQLeafEquiv hb c x) r).1 := by
  rw [literalMarkerQLeafEquiv_value]
  exact ForwardQMarkerCoverage.marker_prefix_projected_point c x r

end DualTree.ForwardQLiteralMarkerLeafEquiv
