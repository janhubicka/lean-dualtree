import DualTree.ForwardQFixedPrefixIso

/-!
# Input-independent direction-labelled geometry of corrected Q

Every corrected Q output has already been identified with the same
fixed source-labelled prefix tree, consisting of old interior nodes
and one terminal for each literal R marker. The remaining LOCAL
geometric datum is the first outgoing direction below each interior
vertex.

At an old interior node s, membership of any realized fixed label
in the cone at s ++ [i] is source-determined: an old label is checked
at its unchanged old vertex, while a terminal label is checked at
its original literal R marker (not at the moving projected point).
This yields input-independent full direction incidence. Combining it
with the previously verified prefix equivalence gives canonical
prefix- and direction-preserving vertex transport between any two
actual corrected Q outputs.

This does not identify the fixed labelled tree with the first-l
homogeneous model of Definition 24: the recursive canonical address
map and the A-to-R boundary equivalence are still open. Nor does it
assert invariance of ambient lengths or forward auxiliary order.
-/

namespace DualTree.ForwardQFixedDirectionIso

open ForwardSourceQTree
open ForwardQFixedVertexShape
open ForwardQMarkerCoverage

/-- The outgoing i-cone at an old interior node, expressed using
only the FIXED source labels. The predicate does not depend on a
corrected mixed-product input or any terminal depth. -/
def FixedChildCone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : OldVertex c) (i : Fin b) :
    FixedShape c → Prop
  | Sum.inl t => IsPrefix (s.1 ++ [i]) t.1
  | Sum.inr r => IsPrefix (s.1 ++ [i]) r.1

/-- Every fixed labelled vertex lies in an outgoing cone of the
realized Q output exactly when its source label lies in that cone.
The nontrivial marker case uses the verified whole old-interior
direction-incidence theorem, not an arbitrary choice of leaves. -/
theorem realize_childCone_iff_fixedChildCone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : OldVertex c) (i : Fin b)
    (u : FixedShape c) :
    IsPrefix (s.1 ++ [i]) (realize c x u).1 ↔
      FixedChildCone c s i u := by
  cases u with
  | inl t =>
      change IsPrefix (s.1 ++ [i]) t.1 ↔
        IsPrefix (s.1 ++ [i]) t.1
      exact Iff.rfl
  | inr r =>
      change IsPrefix (s.1 ++ [i])
        (markedProjection c x (bulletForMarker c r)).1 ↔
        IsPrefix (s.1 ++ [i]) r.1
      exact ForwardQMarkerDirectionalIncidence.oldBase_childCone_projection_iff_marker
        c x r s.1
        ((ForwardQFixedBase.oldBase_mem_iff_original_interior c s.1).2 s.2) i

/-- The FULL direction-incidence signature of each source-labelled
Q vertex, including old-to-old and old-to-terminal directions, is
independent of the corrected mixed-product input. -/
theorem realize_childCone_invariant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (s : OldVertex c) (i : Fin b)
    (u : FixedShape c) :
    IsPrefix (s.1 ++ [i]) (realize c x u).1 ↔
      IsPrefix (s.1 ++ [i]) (realize c y u).1 := by
  exact (realize_childCone_iff_fixedChildCone c x s i u).trans
    (realize_childCone_iff_fixedChildCone c y s i u).symm

/-- The source-labelled vertex transport between genuine Q outputs
preserves AND reflects the whole ambient prefix relation. Unlike
a bare equivalence of vertex types, this is a prefix-tree isomorphism. -/
theorem vertexTransport_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (u v : QVertex c x) :
    IsPrefix u.1 v.1 ↔
      IsPrefix ((vertexTransport hb c x y) u).1
        ((vertexTransport hb c x y) v).1 := by
  obtain ⟨a, ha⟩ := (fixedShapeEquiv hb c x).surjective u
  obtain ⟨d, hd⟩ := (fixedShapeEquiv hb c x).surjective v
  subst u
  subst v
  have htransport (w : FixedShape c) :
      (vertexTransport hb c x y) ((fixedShapeEquiv hb c x) w) =
        (fixedShapeEquiv hb c y) w := by
    simp only [ForwardQFixedVertexShape.vertexTransport,
      Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [htransport a, htransport d]
  simpa only [ForwardQFixedVertexShape.fixedShapeEquiv_apply] using
    (ForwardQFixedPrefixIso.realize_prefix_invariant hb c x y a d)

/-- The same canonical transport also preserves and reflects
every first outgoing direction at every unchanged old interior
node. This is the direction-labelled counterpart of the preceding
prefix-isomorphism theorem. -/
theorem vertexTransport_childCone_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (s : OldVertex c) (i : Fin b)
    (u : QVertex c x) :
    IsPrefix (s.1 ++ [i]) u.1 ↔
      IsPrefix (s.1 ++ [i])
        ((vertexTransport hb c x y) u).1 := by
  obtain ⟨v, hv⟩ := (fixedShapeEquiv hb c x).surjective u
  subst u
  have htransport (w : FixedShape c) :
      (vertexTransport hb c x y) ((fixedShapeEquiv hb c x) w) =
        (fixedShapeEquiv hb c y) w := by
    simp only [ForwardQFixedVertexShape.vertexTransport,
      Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [htransport v]
  simpa only [ForwardQFixedVertexShape.fixedShapeEquiv_apply] using
    (realize_childCone_invariant c x y s i v)

end DualTree.ForwardQFixedDirectionIso
