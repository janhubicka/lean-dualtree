import DualTree.ForwardQModelBoundaryTransport
import DualTree.ForwardQMarkerDirectionalIncidence
import DualTree.ForwardQLiteralSkeletonMeets

/-!
# The genuine corrected Q terminals carry the model-boundary directions

The verified canonical source equivalences identify the first-l model
boundary A_l with original source terminals and then with literal R
first-exit markers. The latter are strictly outside the final source
interior cut.

The geometry of the source is rigid enough to compare first
directions: if r in R is the marker of source terminal t, then
for every original source interior s and direction i,
  s ++ [i] ⊑ t  iff  s ++ [i] ⊑ r.
If r were shorter than this child of s, it would prefix the
interior vertex s, which is impossible for a literal first-exit
marker. The converse is immediate from r ⊑ t.

The already kernel-checked Q directional-incidence theorem equates
the cone of its genuine projected terminal P_r(x) with that of r.
Therefore the FIRST-DIRECTION relation of the genuine Q terminal
indexed by a in A_l agrees with that of its canonical SOURCE leaf,
for all mixed-product inputs x.

This verifies source-to-Q direction labels through the concrete
A_l≃Leaves(S)≃R identification. It does NOT assert that a
source-relative selector on *arbitrary* starred U coincides with
the independent canonical embedding I_U in Definition 24,
nor prove the full Ramsey iteration.
-/

namespace DualTree.ForwardQModelLeafIncidence

open ForwardSourceQTree
open ForwardSourceLeafMarkerEquiv
open ForwardSourceBoundaryEquiv
open ForwardQModelBoundaryTransport

/-- The concrete source-leaf/R equivalence chooses exactly the
literal first-exit marker that prefixes the source leaf.
This is the actual choice underlying the verified equivalence,
not an arbitrary permutation of the finite marker set. -/
theorem sourceLeafMarkerEquiv_prefix
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (t : SourceLeaf c) :
    IsPrefix ((sourceLeafMarkerEquiv hb c) t).1 t.1 := by
  classical
  change IsPrefix
    (Classical.choose (source_leaf_has_marker c t)).1 t.1
  exact Classical.choose_spec (source_leaf_has_marker c t)

/-- The literal marker attached to a first-l model boundary
address is a genuine ambient prefix of the SOURCE terminal
realizing that exact model address. -/
theorem model_marker_prefix_source_leaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (a : ModelA c) :
    IsPrefix ((modelBoundaryMarkerEquiv hb c) a).1
      ((boundarySourceLeafEquiv hb c) a).1 := by
  change IsPrefix
    ((sourceLeafMarkerEquiv hb c)
      ((boundarySourceLeafEquiv hb c) a)).1
    ((boundarySourceLeafEquiv hb c) a).1
  exact sourceLeafMarkerEquiv_prefix hb c
    ((boundarySourceLeafEquiv hb c) a)

/-- An original interior s is an ambient prefix of a source
terminal t precisely when s prefixes t's first-exit R marker.
The marker cannot be a prefix of a source interior vertex. -/
theorem interior_prefix_leaf_iff_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Marker c) (t : SourceLeaf c)
    (hrt : IsPrefix r.1 t.1)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    IsPrefix s t.1 ↔ IsPrefix s r.1 := by
  constructor
  · intro hst
    have hlen : s.length ≤ r.1.length := by
      by_contra hshort
      have hrlen : r.1.length ≤ s.length := Nat.le_of_lt (Nat.lt_of_not_ge hshort)
      have hrs : IsPrefix r.1 s :=
        CutFrontier.prefix_of_prefix_length_le hrt hst hrlen
      exact (ForwardQLiteralSkeletonMeets.literalR_not_prefix_interior
        c r.1 r.2 s hs) hrs
    exact CutFrontier.prefix_of_prefix_length_le hst hrt hlen
  · intro hsr
    exact isPrefix_trans hsr hrt

/-- The outgoing direction at EVERY old source interior vertex
towards a source leaf is identical to the outgoing direction
towards its literal R marker, including stretched source edges. -/
theorem source_leaf_childCone_iff_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Marker c) (t : SourceLeaf c)
    (hrt : IsPrefix r.1 t.1)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    IsPrefix (s ++ [i]) t.1 ↔ IsPrefix (s ++ [i]) r.1 := by
  constructor
  · intro hst
    have hlen : (s ++ [i]).length ≤ r.1.length := by
      by_contra hshort
      have hrlen : r.1.length ≤ s.length := by
        simp only [List.length_append, List.length_singleton] at hshort
        omega
      have hsp : IsPrefix s t.1 :=
        isPrefix_trans ⟨[i], rfl⟩ hst
      have hrs : IsPrefix r.1 s :=
        CutFrontier.prefix_of_prefix_length_le hrt hsp hrlen
      exact (ForwardQLiteralSkeletonMeets.literalR_not_prefix_interior
        c r.1 r.2 s hs) hrs
    exact CutFrontier.prefix_of_prefix_length_le hst hrt hlen
  · intro hsr
    exact isPrefix_trans hsr hrt

/-- A genuinely projected corrected-Q terminal P_r(x) and its
associated original source terminal t occupy EXACTLY the same
first-direction cones from every old interior s. The terminal
depth and local D2 point are irrelevant to this incidence. -/
theorem projected_Q_childCone_iff_source_leaf
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r : Marker c) (t : SourceLeaf c)
    (hrt : IsPrefix r.1 t.1)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    IsPrefix (s ++ [i])
        (markedProjection c x (ForwardQMarkerCoverage.bulletForMarker c r)).1
      ↔ IsPrefix (s ++ [i]) t.1 := by
  have hsOld : s ∈ oldBase c :=
    (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).2 hs
  exact
    (ForwardQMarkerDirectionalIncidence.oldBase_childCone_projection_iff_marker
      c x r s hsOld i).trans
    (source_leaf_childCone_iff_marker c r t hrt s hs i).symm

/-- For the ACTUAL canonical boundary address a in Definition 24,
the corrected Q terminal in coordinate e(a) and the original
source terminal of the same address have identical directional
incidence at ALL original interior nodes. This is the geometric
part needed to identify the canonical I_Q(a) without assuming
anything about arbitrary unrelated starred outputs. -/
theorem model_Q_childCone_iff_source_leaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (a : ModelA c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    IsPrefix (s ++ [i])
        (markedProjection c x (modelAToD2 hb c a)).1
      ↔ IsPrefix (s ++ [i])
        ((boundarySourceLeafEquiv hb c) a).1 := by
  rw [modelAToD2_apply hb c a]
  exact projected_Q_childCone_iff_source_leaf c x
    ((modelBoundaryMarkerEquiv hb c) a)
    ((boundarySourceLeafEquiv hb c) a)
    (model_marker_prefix_source_leaf hb c a)
    s hs i

end DualTree.ForwardQModelLeafIncidence
