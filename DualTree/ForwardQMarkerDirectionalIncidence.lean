import DualTree.ForwardQMarkerRanks

/-!
# Fixed directional attachment of genuine corrected Q terminals

Each literal R marker r has a projected Q terminal P_r(x), depending
on the selected marked point of the corrected mixed input x.

The preceding `oldBase_strictPrefix_projection_iff_marker` theorem
shows that old-interior ancestors of P_r(x) are EXACTLY those of r.
This module strengthens the result from ancestors to their **first
outgoing direction**. At every fixed old-interior node s and every
direction i, the child cone of s labelled i contains P_r(x) iff
it contains r. The assertion is independent of x.

This is a genuinely source-facing necessary invariant for the
canonical A-to-R transport in Definition 24: the direction incidence
of Q leaves is fixed despite variable-depth Q terminals.

It still does not construct the canonical model embedding I_Q or
identify a model boundary address a with its literal marker r.
Those are separate theorems, requiring coherent branching of the
entire fixed interior skeleton and a consistent canonical address
map. No equivalence between paper and corrected starred W_* domains
is asserted.
-/

namespace DualTree.ForwardQMarkerDirectionalIncidence

open ForwardSourceQTree
open ForwardQMarkerCoverage
open ForwardQMarkerRanks

/-- Even at the first direction below an old Q interior node,
the projected Q leaf and the fixed literal marker occupy precisely
the same cone. This is stronger than equality of old ancestor masks. -/
theorem oldBase_childCone_projection_iff_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (s : Node b) (hs : s ∈ oldBase c)
    (i : Fin b) :
    IsPrefix (s ++ [i])
      (markedProjection c x (bulletForMarker c r)).1 ↔
      IsPrefix (s ++ [i]) r.1 := by
  constructor
  · intro hcone
    have hstep : IsStrictPrefix s (s ++ [i]) := by
      refine ⟨⟨[i], rfl⟩, ?_⟩
      intro heq
      have hlen := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hsp :
        IsStrictPrefix s
          (markedProjection c x (bulletForMarker c r)).1 :=
      Lemma27QInterior.strictPrefix_trans_prefix hstep hcone
    have hsr : IsStrictPrefix s r.1 :=
      (oldBase_strictPrefix_projection_iff_marker
        c x r s hs).1 hsp
    have hlen : (s ++ [i]).length ≤ r.1.length := by
      have hlt :=
        MeetClosedFromBranching.length_lt_of_strictPrefix hsr
      simp only [List.length_append, List.length_singleton]
      omega
    exact CutFrontier.prefix_of_prefix_length_le
      hcone (marker_prefix_projected_point c x r) hlen
  · intro hcone
    exact isPrefix_trans hcone
      (marker_prefix_projected_point c x r)

/-- If the selected D₂ points or their depths change, every
literal R marker still determines exactly the same outgoing
direction at each old source interior node. Thus the attachment
direction signature of Q is INPUT-INDEPENDENT. -/
theorem projected_marker_childCone_invariant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    (IsPrefix (s ++ [i])
      (markedProjection c x (bulletForMarker c r)).1 ↔
     IsPrefix (s ++ [i])
      (markedProjection c y (bulletForMarker c r)).1) := by
  have hsBase : s ∈ oldBase c :=
    (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).2 hs
  exact (oldBase_childCone_projection_iff_marker
    c x r s hsBase i).trans
    (oldBase_childCone_projection_iff_marker
      c y r s hsBase i).symm

end DualTree.ForwardQMarkerDirectionalIncidence
