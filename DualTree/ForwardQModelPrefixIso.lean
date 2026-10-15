import DualTree.ForwardSourceAddressPrefixIso
import DualTree.ForwardQModelLeafIncidence
import DualTree.ForwardQFixedPrefixIso

/-!
# Exact model prefix-tree isomorphism for every corrected Q output

The full finite homogeneous model shape consists of the first l
breadth-first interior addresses and all their external children.
The previous development proved a genuine vertex bijection with
each corrected Q output, but relation invariance between different
Q outputs alone does not show that this bijection respects the
MODEL's own prefix relation.

Here that obligation is discharged:
* model interior/interior prefixes correspond to original source
  interior prefixes, via the reflected admissible source walk;
* model interior/model boundary prefixes correspond to source
  interior/source leaf prefixes, via the same address map;
* the original source leaf and its literal R first-exit marker
  have exactly the same old-interior predecessor mask;
* model boundary vertices do not prefix interior vertices;
* distinct model boundary vertices and distinct Q projected
  leaves are incomparable.

Consequently the model-to-Q bijection preserves AND reflects
the WHOLE ambient PREFIX order for ALL actual corrected mixed
inputs. This is a genuine prefix-tree isomorphism and goes beyond
the earlier input-to-input Q prefix invariance.

The remaining direction-labelled assertion still requires a
model-child to source-successor first-direction theorem.
Definition 24's canonical I_U for arbitrary semi-complete starred
U is not silently identified by these results.
-/

namespace DualTree.ForwardQModelPrefixIso

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceBoundaryEquiv
open ForwardSourceLeafMarkerEquiv
open ForwardSourceInteriorFirstL
open ForwardQModelVertexEquiv
open ForwardQModelBoundaryTransport
open ForwardQFixedVertexShape
open ForwardQFixedPrefixIso
open ForwardModelBoundaryHeap

/-- The canonical boundary-to-source-leaf equivalence realizes
an external model address by the exact same root-directed
source support walk as every other canonical source address. -/
theorem boundarySourceLeafEquiv_value
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : ModelA c) :
    ((boundarySourceLeafEquiv hb c) a).1 =
      CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) a.1 := by
  rfl

/-- The original source interior vertex of a first-l model
address lies on the path to the original source terminal of
a boundary address iff the MODEL address itself is a prefix
of that boundary address. This is the source realization
part of the canonical model/Q prefix correspondence. -/
theorem modelInterior_boundary_source_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (p : ModelInteriorVertex c)
    (a : ModelA c) :
    IsPrefix p.1 a.1 ↔
      IsPrefix ((modelInteriorSourceEquiv hb c) p).1
        ((boundarySourceLeafEquiv hb c) a).1 := by
  have hcount := cut_heapIndex_succ_eq_l hb c
  have hple : heapIndex p.1 ≤ heapIndex
      (ForwardSourceAddressOrder.cutAddress c).1 := by
    have hp : heapIndex p.1 < l := p.2
    omega
  let u : SourceAddress c :=
    ⟨p.1, ForwardSourceHeapInitial.heap_le_cut_admissible
      hb c p.1 hple⟩
  let v : SourceAddress c :=
    ⟨a.1, ForwardSourceBoundaryLeaves.modelBoundary_admissible
      hb c a⟩
  rw [ForwardSourceAddressPrefixIso.modelInteriorSourceEquiv_value
    hb c p, boundarySourceLeafEquiv_value hb c a]
  exact ForwardSourceAddressPrefixIso.sourceAddress_prefix_iff c u v

/-- The actual underlying homogeneous model word of a
two-sorted vertex label (inside the first-l interior or its
external boundary). -/
def modelAddress
    {b n l k m : Nat} {α : Type*}
    {c : Frame b n l k m α} :
    ModelShape c → Node b
  | Sum.inl a => a.1
  | Sum.inr a => a.1

/-- Prefix relation on the homogeneous model shape; external
model boundary points are mutually incomparable and never
prefix an interior point. -/
def ModelPrefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    ModelShape c → ModelShape c → Prop
  | Sum.inl a, Sum.inl d => IsPrefix a.1 d.1
  | Sum.inl a, Sum.inr d => IsPrefix a.1 d.1
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr a, Sum.inr d => a = d

/-- This abstract two-sorted model prefix relation is
EXACTLY the ambient initial-segment ordering on the
corresponding homogeneous model words. -/
theorem modelPrefix_iff_ambientPrefix
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (u v : ModelShape c) :
    ModelPrefix c u v ↔
      IsPrefix (modelAddress u) (modelAddress v) := by
  cases u with
  | inl a =>
      cases v with
      | inl d => exact Iff.rfl
      | inr d => exact Iff.rfl
  | inr a =>
      cases v with
      | inl d =>
          change False ↔ IsPrefix a.1 d.1
          constructor
          · exact False.elim
          · intro hprefix
            have hinside : ModelInterior l a.1 :=
              modelInterior_prefix_closed hb hprefix d.2
            exact (a.2.1 hinside).elim
      | inr d =>
          change a = d ↔ IsPrefix a.1 d.1
          constructor
          · intro heq
            subst d
            exact isPrefix_refl _
          · intro hprefix
            exact Subtype.ext
              (modelBoundary_antichain hb a.2 d.2 hprefix)

/-- The source-labelled fixed Q prefix relation coincides
with the model's ACTUAL prefix relation under the concrete
canonical model-to-fixed-shape equivalence, including the
nontrivial source-interior-to-literal-marker case. -/
theorem modelShape_FixedPrefix_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (u v : ModelShape c) :
    FixedPrefix c ((modelShapeEquiv hb c) u)
      ((modelShapeEquiv hb c) v) ↔
    ModelPrefix c u v := by
  cases u with
  | inl a =>
      cases v with
      | inl d =>
          change
            IsPrefix ((modelInteriorSourceEquiv hb c) a).1
              ((modelInteriorSourceEquiv hb c) d).1 ↔
            IsPrefix a.1 d.1
          exact
            (ForwardSourceAddressPrefixIso.modelInterior_source_prefix_iff
              hb c a d).symm
      | inr d =>
          let s : OldVertex c := (modelInteriorSourceEquiv hb c) a
          let r : Marker c := (modelBoundaryMarkerEquiv hb c) d
          let t : SourceLeaf c := (boundarySourceLeafEquiv hb c) d
          change IsStrictPrefix s.1 r.1 ↔ IsPrefix a.1 d.1
          have hrt : IsPrefix r.1 t.1 :=
            ForwardQModelLeafIncidence.model_marker_prefix_source_leaf
              hb c d
          have hsource : IsPrefix s.1 t.1 ↔ IsPrefix s.1 r.1 :=
            ForwardQModelLeafIncidence.interior_prefix_leaf_iff_marker
              c r t hrt s.1 s.2
          have hmodel : IsPrefix a.1 d.1 ↔ IsPrefix s.1 t.1 :=
            modelInterior_boundary_source_prefix_iff hb c a d
          have hstrict : IsStrictPrefix s.1 r.1 ↔
              IsPrefix s.1 r.1 := by
            constructor
            · intro h
              exact h.1
            · intro h
              refine ⟨h, ?_⟩
              intro heq
              have hrsp : IsPrefix r.1 s.1 := by
                rw [heq]
                exact isPrefix_refl _
              exact
                (ForwardQLiteralSkeletonMeets.literalR_not_prefix_interior
                  c r.1 r.2 s.1 s.2) hrsp
          exact hstrict.trans (hsource.symm.trans hmodel.symm)
  | inr a =>
      cases v with
      | inl d =>
          change False ↔ False
          exact Iff.rfl
      | inr d =>
          change
            (modelBoundaryMarkerEquiv hb c) a =
              (modelBoundaryMarkerEquiv hb c) d ↔
            a = d
          constructor
          · exact (modelBoundaryMarkerEquiv hb c).injective
          · intro heq
            simp [heq]

/-- The actual corrected Q realisation of the first-l
homogeneous interior-plus-boundary model preserves AND
reflects ALL model prefix comparisons, with no assumptions
about equal ambient depths of different Q terminals. -/
theorem modelQ_prefix_iff_ModelPrefix
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (u v : ModelShape c) :
    IsPrefix ((modelQVertexEquiv hb c x) u).1
      ((modelQVertexEquiv hb c x) v).1 ↔
    ModelPrefix c u v := by
  have hfixed :=
    ForwardQFixedPrefixIso.realize_prefix_iff_fixedPrefix
      hb c x ((modelShapeEquiv hb c) u)
        ((modelShapeEquiv hb c) v)
  have hmodel :=
    modelShape_FixedPrefix_iff hb c u v
  simpa only [modelQVertexEquiv, Equiv.trans_apply,
    ForwardQFixedVertexShape.fixedShapeEquiv_apply]
    using hfixed.trans hmodel

/-- In the precise sense of the original model's AMBIENT
initial-segment relation, the source-facing repaired Q
canonical realisation is a full prefix-tree isomorphism. -/
theorem modelQ_prefix_iff_modelAddress
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (u v : ModelShape c) :
    IsPrefix ((modelQVertexEquiv hb c x) u).1
      ((modelQVertexEquiv hb c x) v).1 ↔
    IsPrefix (modelAddress u) (modelAddress v) := by
  exact (modelQ_prefix_iff_ModelPrefix hb c x u v).trans
    (modelPrefix_iff_ambientPrefix hb c u v)

end DualTree.ForwardQModelPrefixIso
