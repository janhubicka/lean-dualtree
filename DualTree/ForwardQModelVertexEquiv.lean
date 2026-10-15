import DualTree.ForwardQModelLeafIncidence
import DualTree.ForwardQFixedPrefixIso
import DualTree.ForwardQFixedDirectionIso
import DualTree.ForwardQFixedRank
import DualTree.ForwardSourceInteriorFirstL

/-!
# A canonical model-labelled vertex equivalence for corrected Q

The corrected source geometry supplies:
  H_l := first l homogeneous heap addresses
         ≃ original source interior vertices;
  A_l := external homogeneous first-l boundary
         ≃ literal first-exit markers R.

All genuine corrected Q outputs have the exact fixed two-sorted
shape Int(S) ⊕ R, and its realization is bijective, with
prefix-order, source-interior first-direction and intrinsic-rank
invariants independent of the moving D2 terminal depths.

This file packages these statements into one precise equiv
  (H_l ⊕ A_l) ≃ Q(c,x)
for EVERY actual corrected mixed input x.

The interior point at an address a is exactly the canonical
original source interior at a; the boundary point at a is exactly
the projected true D2 leaf indexed by the canonical A_l≃R≃D2
equivalence. We also verify input independence of ALL prefix
relations, outgoing directions at old interior nodes, and
intrinsic ranks through this address-preserving matching.

This is a canonical labelled VERTEX equivalence, not yet the
full isomorphism of the ambient model's own prefix/direction
relations with Q. That last assertion needs the directional
walk's model-to-source prefix/child incidence lemma.
Consequently this is not silently identified with the
published Definition 24 map I_U on arbitrary starred U.
-/

namespace DualTree.ForwardQModelVertexEquiv

open ForwardSourceQTree
open ForwardSourceInteriorFirstL
open ForwardSourceAddressOrder
open ForwardModelBoundaryHeap
open ForwardSourceBoundaryEquiv
open ForwardQModelBoundaryTransport
open ForwardQFixedVertexShape

/-- Genuine first-l homogeneous interior addresses of the
source's prescribed l, with corrected forward heap order. -/
abbrev ModelInteriorVertex
    {b n l k m : Nat} {α : Type*}
    (_c : Frame b n l k m α) :=
  {a : Node b // ModelInterior l a}

/-- The full two-sorted model shape, including the genuine
external first-l boundary rather than its arbitrary enumeration. -/
abbrev ModelShape
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ModelInteriorVertex c ⊕ ModelA c

/-- The actual first-l interior is canonically equivalent to
the original source interior, using the checked cut cardinality
rather than assuming that first-l address realizations are onto. -/
noncomputable def modelInteriorSourceEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    ModelInteriorVertex c ≃ OldVertex c := by
  let hcount := cut_heapIndex_succ_eq_l hb c
  let e : ModelInteriorVertex c ≃ InitialCutModel c := {
    toFun := fun a => ⟨a.1, by
      change ModelInterior
        (heapIndex (cutAddress c).1 + 1) a.1
      simpa only [hcount] using a.2⟩
    invFun := fun a => ⟨a.1, by
      change ModelInterior l a.1
      have ha : ModelInterior
          (heapIndex (cutAddress c).1 + 1) a.1 := a.2
      simpa only [hcount] using ha⟩
    left_inv := by
      intro a
      apply Subtype.ext
      rfl
    right_inv := by
      intro a
      apply Subtype.ext
      rfl
  }
  exact e.trans (initialCutInteriorEquiv hb c)

/-- The model first-l interior and boundary, without any
arbitrary sorting, identify with the fixed source-labelled
interior and R-marker shape of every corrected Q output. -/
noncomputable def modelShapeEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    ModelShape c ≃ FixedShape c :=
  Equiv.sumCongr
    (modelInteriorSourceEquiv hb c)
    (modelBoundaryMarkerEquiv hb c)

/-- The canonical model-labelled vertex equivalence into
any actual corrected Q output. Its terminal values may move
as the selected D2 mixed-product marked points vary. -/
noncomputable def modelQVertexEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    ModelShape c ≃ QVertex c x :=
  (modelShapeEquiv hb c).trans (fixedShapeEquiv hb c x)

/-- A canonical MODEL INTERIOR address maps to its unchanged
original source interior node, independent of Q mixed input. -/
theorem modelQ_interior_value
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (a : ModelInteriorVertex c) :
    ((modelQVertexEquiv hb c x) (Sum.inl a)).1 =
      ((modelInteriorSourceEquiv hb c) a).1 := by
  rfl

/-- A canonical MODEL BOUNDARY address maps exactly to the
genuine Q projected marked terminal indexed by A_l≃R≃D2. -/
theorem modelQ_terminal_value
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (a : ModelA c) :
    ((modelQVertexEquiv hb c x) (Sum.inr a)).1 =
      (markedProjection c x (modelAToD2 hb c a)).1 := by
  change (markedProjection c x
    (ForwardQMarkerCoverage.bulletForMarker c
      ((modelBoundaryMarkerEquiv hb c) a))).1 =
    (markedProjection c x (modelAToD2 hb c a)).1
  rw [modelAToD2_apply hb c a]

/-- For every two actual corrected Q inputs, the CANONICAL
model address matching preserves and reflects ambient
prefix order of all interior and boundary model vertices. -/
theorem modelQ_prefix_invariant
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (u v : ModelShape c) :
    IsPrefix ((modelQVertexEquiv hb c x) u).1
      ((modelQVertexEquiv hb c x) v).1 ↔
    IsPrefix ((modelQVertexEquiv hb c y) u).1
      ((modelQVertexEquiv hb c y) v).1 := by
  simpa only [modelQVertexEquiv, Equiv.trans_apply,
    ForwardQFixedVertexShape.fixedShapeEquiv_apply] using
    (ForwardQFixedPrefixIso.realize_prefix_invariant
      hb c x y ((modelShapeEquiv hb c) u)
        ((modelShapeEquiv hb c) v))

/-- Every model address label has the same outgoing-direction
membership at every OLD ORIGINAL SOURCE INTERIOR node, in any
two actual corrected Q outputs. No ambient depth equality
of moving terminals is presumed. -/
theorem modelQ_childCone_invariant
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (s : OldVertex c) (i : Fin b)
    (u : ModelShape c) :
    IsPrefix (s.1 ++ [i]) ((modelQVertexEquiv hb c x) u).1 ↔
    IsPrefix (s.1 ++ [i]) ((modelQVertexEquiv hb c y) u).1 := by
  simpa only [modelQVertexEquiv, Equiv.trans_apply,
    ForwardQFixedVertexShape.fixedShapeEquiv_apply] using
    (ForwardQFixedDirectionIso.realize_childCone_invariant
      c x y s i ((modelShapeEquiv hb c) u))

/-- Intrinsic Q ranks on the whole canonical model vertex
type are input-independent, even though the ambient
lengths of selected projected terminal leaves need not be. -/
theorem modelQ_intrinsic_rank_invariant
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (u : ModelShape c) :
    SkewTree.heightAt (nodes c x).toList
      ((modelQVertexEquiv hb c x) u).1 =
    SkewTree.heightAt (nodes c y).toList
      ((modelQVertexEquiv hb c y) u).1 := by
  simpa only [modelQVertexEquiv, Equiv.trans_apply,
    ForwardQFixedVertexShape.fixedShapeEquiv_apply] using
    (ForwardQFixedRank.realize_height_invariant
      c x y ((modelShapeEquiv hb c) u))

end DualTree.ForwardQModelVertexEquiv
