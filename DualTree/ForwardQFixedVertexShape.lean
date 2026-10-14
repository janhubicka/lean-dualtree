import DualTree.ForwardQLiteralMarkerLeafEquiv
import DualTree.ForwardQMarkerDirectionalIncidence

/-!
# A fixed two-sorted vertex shape for every genuine corrected Q output

The corrected Q tree has exactly the original source interior plus one
terminal for each literal first-exit marker r in the FIXED set R.
The terminal corresponding to r is the actual projected point P_r(x),
which can move with the mixed-product input x.

This module packages that structural fact as a source-independent
two-sorted type, `FixedShape c`, and establishes for every actual
input x a bijection

    FixedShape c ≃ {s // s ∈ Q(c,x)}.

In particular any two Q outputs have canonically corresponding
vertices: each old interior node is identified with itself and
each moving terminal is identified by the SAME literal R marker.

This is an equivalence of VERTEX TYPES. Preservation and reflection
of rooted prefix order and direction labels are further obligations;
these are deliberately not hidden in the name or statement of the
equivalence. The previous verified direction-incidence lemma gives
the main geometric ingredient for that strengthening.

No arbitrary marker order, choice of a Q input, or cardinality
argument is used.
-/

namespace DualTree.ForwardQFixedVertexShape

open ForwardSourceQTree
open ForwardQMarkerCoverage
open ForwardQLiteralMarkerLeafEquiv

/-- The fixed old interior, common to every output Q(c,x). -/
abbrev OldVertex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {s : Node b // s ∈ SkewTree.interior c.source.tree}

/-- The literal R marker type depends only on the source frame. -/
abbrev FixedMarker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardSortedMixedProduct.Marker c.source c.cut c.hout

/-- The fixed underlying abstract shape: old interior vertices,
then individually labelled literal R boundary terminals. -/
abbrev FixedShape
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  OldVertex c ⊕ FixedMarker c

/-- Actual vertices of one input-dependent corrected Q tree. -/
abbrev QVertex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :=
  {s : Node b // s ∈ (nodes c x).toList}

/-- Realize a fixed-shape vertex in the actual Q output:
old interior nodes do not move; each R terminal is projected
using its actual selected D₂ point. -/
noncomputable def realize
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) : FixedShape c → QVertex c x
  | Sum.inl s =>
      ⟨s.1, Finset.mem_toList.mpr
        (ForwardQFixedBase.originalInterior_mem_Q c x s.1 s.2)⟩
  | Sum.inr r =>
      ⟨(markedProjection c x (bulletForMarker c r)).1,
        Finset.mem_toList.mpr
          (markedProjection_mem c x (bulletForMarker c r))⟩

/-- Distinct fixed-shape vertices yield distinct actual Q nodes.
In the mixed cases this uses the exact old-interior/terminal
dichotomy, not an arbitrary enumeration of the leaves. -/
theorem realize_injective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    Function.Injective (realize c x) := by
  intro u v huv
  cases u with
  | inl s =>
      cases v with
      | inl t =>
          have heq : s.1 = t.1 := congrArg (fun q : QVertex c x => q.1) huv
          exact congrArg Sum.inl (Subtype.ext heq)
      | inr r =>
          have heq : s.1 =
              (markedProjection c x (bulletForMarker c r)).1 :=
            congrArg (fun q : QVertex c x => q.1) huv
          have hi : s.1 ∈ SkewTree.interior (nodes c x).toList :=
            (ForwardQInteriorExact.Q_interior_iff_original
              hb c x s.1).2 s.2
          have hterminal :=
            ForwardQSourceTerminals.markedProjection_terminal
              c x (bulletForMarker c r)
          have hbad :
              (markedProjection c x (bulletForMarker c r)).1 ∈
                SkewTree.interior (nodes c x).toList := by
            rw [← heq]
            exact hi
          exact False.elim (hterminal hbad)
  | inr r =>
      cases v with
      | inl s =>
          have heq :
              (markedProjection c x (bulletForMarker c r)).1 =
                s.1 :=
            congrArg (fun q : QVertex c x => q.1) huv
          have hi : s.1 ∈ SkewTree.interior (nodes c x).toList :=
            (ForwardQInteriorExact.Q_interior_iff_original
              hb c x s.1).2 s.2
          have hterminal :=
            ForwardQSourceTerminals.markedProjection_terminal
              c x (bulletForMarker c r)
          have hbad :
              (markedProjection c x (bulletForMarker c r)).1 ∈
                SkewTree.interior (nodes c x).toList := by
            rw [heq]
            exact hi
          exact False.elim (hterminal hbad)
      | inr t =>
          have heq :
              (markedProjection c x (bulletForMarker c r)).1 =
              (markedProjection c x (bulletForMarker c t)).1 :=
            congrArg (fun q : QVertex c x => q.1) huv
          have hbullet : bulletForMarker c r = bulletForMarker c t :=
            markedProjection_injective c x (Subtype.ext heq)
          have hrt : r = t :=
            (literalMarkerBulletEquiv c).injective hbullet
          exact congrArg Sum.inr hrt

/-- Every actual Q vertex is either a fixed old interior node or
the projected image of precisely one fixed literal R marker. -/
theorem realize_surjective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    Function.Surjective (realize c x) := by
  intro q
  by_cases hint :
      q.1 ∈ SkewTree.interior (nodes c x).toList
  · let s : OldVertex c :=
      ⟨q.1, (ForwardQInteriorExact.Q_interior_iff_original
        hb c x q.1).1 hint⟩
    refine ⟨Sum.inl s, ?_⟩
    apply Subtype.ext
    rfl
  · let leaf : QLeaf c x := ⟨q.1, ⟨q.2, hint⟩⟩
    obtain ⟨j, hj⟩ := Q_leaf_has_bullet hb c x leaf
    obtain ⟨r, hr⟩ := (literalMarkerBulletEquiv c).surjective j
    refine ⟨Sum.inr r, ?_⟩
    apply Subtype.ext
    change (markedProjection c x (bulletForMarker c r)).1 = q.1
    change bulletForMarker c r = j at hr
    rw [hr]
    exact hj

/-- Every genuine corrected Q output has the same fixed source-labelled
vertex type, though its actual terminal positions can differ. -/
noncomputable def fixedShapeEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    FixedShape c ≃ QVertex c x :=
  Equiv.ofBijective (realize c x)
    ⟨realize_injective hb c x, realize_surjective hb c x⟩

/-- Canonical vertex matching between TWO corrected Q outputs,
through the common old-interior + literal-R label type.

This is an equivalence of vertex sets, NOT YET an order isomorphism. -/
noncomputable def vertexTransport
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c) :
    QVertex c x ≃ QVertex c y :=
  (fixedShapeEquiv hb c x).symm.trans
    (fixedShapeEquiv hb c y)

end DualTree.ForwardQFixedVertexShape
