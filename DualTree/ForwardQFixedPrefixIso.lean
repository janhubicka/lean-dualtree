import DualTree.ForwardQFixedVertexShape
import DualTree.ForwardQRelativeMarkerSelector

/-!
# The exact fixed prefix-tree shape of corrected Q outputs

The previous module identifies every actual corrected Q output as a
fixed old-interior vertex type plus one vertex for every literal R
marker. This module establishes that the correspondence also
preserves and reflects the AMBIENT PREFIX ORDER.

On fixed labels the relation is:
  old s  ≤ old t   iff s is a prefix of t;
  old s  ≤ marker r iff s is a STRICT prefix of r;
  marker ≤ old     never;
  marker r ≤ marker t iff r=t.

For any actual Q input x the realization map preserves and reflects
this relation. Therefore all outputs Q(x), Q(y) have the SAME prefix
poset through the canonical fixed source-labelled vertex matching,
even when their terminal positions and depths differ.

This is stronger than an abstract bijection or a counting argument.
It does NOT yet construct the direction-labelled canonical embedding
of Definition 24 from the first-l homogeneous model, or establish
the mixed-product Ramsey iteration. A prefix-tree isomorphism alone
does not preserve ambient first directions without a further lemma.
-/

namespace DualTree.ForwardQFixedPrefixIso

open ForwardSourceQTree
open ForwardQMarkerCoverage
open ForwardQFixedVertexShape
open ForwardQLiteralMarkerLeafEquiv

/-- The source-determined prefix relation on fixed old-interior
vertices and fixed literal R terminals. It does not refer to
any particular mixed-product input. -/
def FixedPrefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    FixedShape c → FixedShape c → Prop
  | Sum.inl s, Sum.inl t => IsPrefix s.1 t.1
  | Sum.inl s, Sum.inr r => IsStrictPrefix s.1 r.1
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr r, Sum.inr t => r = t

/-- The actual prefix relation among Q vertices is EXACTLY
the same fixed relation on source labels, for every x.
In particular, no moving projected terminal introduces
a new old-interior ancestor or moves into a different old
branch, and distinct terminals remain incomparable. -/
theorem realize_prefix_iff_fixedPrefix
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (u v : FixedShape c) :
    IsPrefix (realize c x u).1 (realize c x v).1 ↔
      FixedPrefix c u v := by
  cases u with
  | inl s =>
      cases v with
      | inl t =>
          change IsPrefix s.1 t.1 ↔ IsPrefix s.1 t.1
          exact Iff.rfl
      | inr r =>
          change IsPrefix s.1
            (markedProjection c x (bulletForMarker c r)).1 ↔
            IsStrictPrefix s.1 r.1
          have hsBase : s.1 ∈ oldBase c :=
            (ForwardQFixedBase.oldBase_mem_iff_original_interior c s.1).2 s.2
          constructor
          · intro hpre
            have hneq : s.1 ≠
                (markedProjection c x (bulletForMarker c r)).1 := by
              intro heq
              have hi : s.1 ∈ SkewTree.interior (nodes c x).toList :=
                (ForwardQInteriorExact.Q_interior_iff_original
                  hb c x s.1).2 s.2
              have hterminal :=
                ForwardQSourceTerminals.markedProjection_terminal
                  c x (bulletForMarker c r)
              apply hterminal
              rw [← heq]
              exact hi
            exact (ForwardQMarkerRanks.oldBase_strictPrefix_projection_iff_marker
              c x r s.1 hsBase).1 ⟨hpre, hneq⟩
          · intro hstrict
            exact ((ForwardQMarkerRanks.oldBase_strictPrefix_projection_iff_marker
              c x r s.1 hsBase).2 hstrict).1
  | inr r =>
      cases v with
      | inl s =>
          change IsPrefix
            (markedProjection c x (bulletForMarker c r)).1 s.1 ↔ False
          constructor
          · intro hpre
            have hsBase : s.1 ∈ oldBase c :=
              (ForwardQFixedBase.oldBase_mem_iff_original_interior c s.1).2 s.2
            have hsEarly : ForwardAux s.1 c.cut :=
              ForwardQFixedBase.oldBase_before_cut c s.1 hsBase
            have hrOld : IsPrefix r.1 s.1 :=
              isPrefix_trans
                (marker_prefix_projected_point c x r) hpre
            have hrEarly : ForwardAux r.1 c.cut :=
              ForwardInclusiveFrontier.forwardAux_of_prefix hrOld hsEarly
            exact (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
              c.source c.cut c.hcut c.hmax c.hout r.1 r.2).1 hrEarly
          · exact False.elim
      | inr t =>
          change IsPrefix
            (markedProjection c x (bulletForMarker c r)).1
            (markedProjection c x (bulletForMarker c t)).1 ↔ r = t
          constructor
          · intro hpre
            have hrtPrefix : IsPrefix r.1
                (markedProjection c x (bulletForMarker c t)).1 :=
              isPrefix_trans (marker_prefix_projected_point c x r) hpre
            have hterminal :
                (markedProjection c x (bulletForMarker c t)).1 ∈
                  (nodes c x).toList ∧
                (markedProjection c x (bulletForMarker c t)).1 ∉
                  SkewTree.interior (nodes c x).toList := by
              exact ⟨Finset.mem_toList.mpr
                  (markedProjection_mem c x (bulletForMarker c t)),
                ForwardQSourceTerminals.markedProjection_terminal
                  c x (bulletForMarker c t)⟩
            have hpoints :
                (markedProjection c x (bulletForMarker c t)).1 =
                (markedProjection c x (bulletForMarker c r)).1 :=
              ForwardQRelativeMarkerSelector.Q_leaf_unique_above_literal_marker
                hb c x r _ hterminal hrtPrefix
            have hbullets :
                bulletForMarker c t = bulletForMarker c r :=
              markedProjection_injective c x (Subtype.ext hpoints)
            exact ((literalMarkerBulletEquiv c).injective hbullets).symm
          · intro heq
            subst t
            exact isPrefix_refl _

/-- The full prefix relation between any two fixed vertices is
independent of the selected mixed-product point, even when all
the projected terminal depths move. -/
theorem realize_prefix_invariant
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (u v : FixedShape c) :
    IsPrefix (realize c x u).1 (realize c x v).1 ↔
      IsPrefix (realize c y u).1 (realize c y v).1 := by
  exact (realize_prefix_iff_fixedPrefix hb c x u v).trans
    (realize_prefix_iff_fixedPrefix hb c y u v).symm

end DualTree.ForwardQFixedPrefixIso
