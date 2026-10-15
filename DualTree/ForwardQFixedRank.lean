import DualTree.ForwardQFixedDirectionIso
import DualTree.ForwardQIntrinsicRanks
import DualTree.ForwardQMarkerRanks

/-!
# Input-independent intrinsic levels on the fixed corrected Q shape

The previous modules construct a common old-interior-plus-R vertex
shape and prove that every genuine corrected Q realization has the
same prefix order and outgoing interior directions.

An additional essential ingredient for the canonical Definition 24
address system is the intrinsic rank of each vertex. Every Q strict
predecessor is in the fixed old interior, and a moving terminal has
exactly the old-interior predecessor mask of its literal R marker.

Consequently the entire Q intrinsic level function factors through
the fixed source labels. This holds for *every* corrected mixed input,
without assuming a particular marked-point length order: it counts
intrinsic predecessors rather than ambient depths.

The theorem does not identify this source-labelled levelled tree with
the first-l forward homogeneous model or construct A-to-R transport.
-/

namespace DualTree.ForwardQFixedRank

open ForwardSourceQTree
open ForwardQFixedVertexShape
open ForwardQMarkerCoverage

/-- The intrinsic rank of a fixed Q vertex label is the number of
fixed source interior nodes properly preceding its source position.
This uses an old ambient node for old labels and the literal first-exit
marker for new terminal labels, not the moving projected Q position. -/
noncomputable def FixedRank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    FixedShape c → Nat
  | Sum.inl s =>
      ((SkewTree.interior c.source.tree).toFinset.filter
        (fun t => SkewTree.strictPrefixB t s.1 = true)).card
  | Sum.inr r =>
      ((SkewTree.interior c.source.tree).toFinset.filter
        (fun t => SkewTree.strictPrefixB t r.1 = true)).card

/-- The Q intrinsic rank of every actual fixed-labelled vertex is
exactly the fixed source rank. The terminal proof uses the verified
literal-R predecessor-mask equality for the genuine projected point. -/
theorem realize_height_eq_FixedRank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) (u : FixedShape c) :
    SkewTree.heightAt (nodes c x).toList (realize c x u).1 =
      FixedRank c u := by
  cases u with
  | inl s =>
      change SkewTree.heightAt (nodes c x).toList s.1 =
        ((SkewTree.interior c.source.tree).toFinset.filter
          (fun t => SkewTree.strictPrefixB t s.1 = true)).card
      exact ForwardQIntrinsicRanks.Q_height_eq_original_interior_prefix_card
        c x s.1 (ForwardQFixedBase.originalInterior_mem_Q c x s.1 s.2)
  | inr r =>
      change SkewTree.heightAt (nodes c x).toList
        (markedProjection c x (bulletForMarker c r)).1 =
        ((SkewTree.interior c.source.tree).toFinset.filter
          (fun t => SkewTree.strictPrefixB t r.1 = true)).card
      exact ForwardQMarkerRanks.markedProjection_height_eq_marker_prefix_card
        c x r

/-- Moving projected terminals may change their ambient depths,
but never their intrinsic Q rank. This assertion applies to every
fixed old-interior or literal-R terminal label. -/
theorem realize_height_invariant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c) (u : FixedShape c) :
    SkewTree.heightAt (nodes c x).toList (realize c x u).1 =
      SkewTree.heightAt (nodes c y).toList (realize c y u).1 := by
  exact (realize_height_eq_FixedRank c x u).trans
    (realize_height_eq_FixedRank c y u).symm

/-- The canonical input-to-input vertex transport additionally
preserves the intrinsic Q rank, not just prefixes and outgoing
directions. Together these are the geometry invariants required
before building the coherent Definition 24 model addresses. -/
theorem vertexTransport_height_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : Input c)
    (u : QVertex c x) :
    SkewTree.heightAt (nodes c x).toList u.1 =
      SkewTree.heightAt (nodes c y).toList
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
    (realize_height_invariant c x y v)

end DualTree.ForwardQFixedRank
