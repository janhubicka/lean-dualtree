import DualTree.ForwardQFinalSupportCut
import DualTree.ForwardCompletePrefixIso
import DualTree.ForwardProjectedTerminalOrder

/-!
# Recover exact local prefix and global forward-order comparisons after projection

The final Lemma 27 ambient refinement f' uses new variable roots
P_i(z) in the COMPLETE ambient support T, rather than identifying
local cone variables with the old l roots of Q(w).

The previous modules prove all P_i(z) are jointly injective and
split them from the retained initial-cut support. For complete
skew-tree gluing, two stronger properties are needed:

1. INSIDE each frontier, the canonical projection both preserves
   AND reflects initial-segment order. Reflection follows by
   transporting a support prefix through the checked inverse
   address and cancelling the fixed frontier address.
2. ACROSS frontier coordinates i<j, if the local tail lengths
   satisfy |z|<=|w|, the projected ambient T nodes are in the
   corrected forward auxiliary order, hence their ambient
   lengths are nondecreasing. This invokes the existing
   frontier-rank plus length-order comparison for T.

The local words' vector-completeness will later supply the
required tail-length inequalities at equal and consecutive
intrinsic levels; that is deliberately NOT assumed here.
No complete-skew property for the candidate T' is claimed
by these conditional transport facts alone.
-/

namespace DualTree.ForwardQFinalProjectionOrder

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQActualCoordinateWord
open ForwardQFinalSupportCut

/-- Inside the SAME frontier, canonical projection reflects
as well as preserves the ambient prefix order. Stretched
support edges do not affect the inverse address calculation. -/
theorem projected_same_frontier_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k - (m + 1))) :
    IsPrefix (projected c ⟨i,z⟩).1 (projected c ⟨i,w⟩).1 ↔
      IsPrefix z.1 w.1 := by
  constructor
  · intro h
    have hpre :
        IsPrefix
          (ForwardCompleteBijection.inverseAddress
            c.T c.hcomplete c.hnon (projectLocal c i z)).1
          (ForwardCompleteBijection.inverseAddress
            c.T c.hcomplete c.hnon (projectLocal c i w)).1 :=
      ForwardCompletePrefixIso.inverseAddress_prefix
        c.T c.hcomplete c.hnon
        (projectLocal c i z) (projectLocal c i w) h
    rw [ForwardQActualCoordinateWord.projectLocal_inverse c i z,
      ForwardQActualCoordinateWord.projectLocal_inverse c i w]
      at hpre
    obtain ⟨tail, htail⟩ := hpre
    refine ⟨tail, ?_⟩
    have hcancel :
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon
          (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++
          w.1 =
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon
          (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++
          (z.1 ++ tail) := by
      simpa [List.append_assoc] using htail
    exact List.append_cancel_left hcancel
  · intro hpre
    exact projected_same_frontier_prefix c i z w hpre

/-- Projected ambient nodes have EXACT support ranks,
using the genuine frontier rank plus the local tail length. -/
theorem projected_height
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    SkewTree.heightAt c.T (projected c u).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1 +
        u.2.1.length := by
  exact ForwardUniformConeDomains.projectCommon_height
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut u.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut u.1)
    u.2

/-- Between distinct ORDERED frontiers, nondecreasing local
tail lengths imply the corrected forward auxiliary order
of the actual projected T vertices. No equality between
ambient length and intrinsic support rank is assumed. -/
theorem projected_forward_order_of_tail_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : LocalAddress c)
    (hij : u.1 < v.1)
    (hlength : u.2.1.length ≤ v.2.1.length) :
    ForwardAux (projected c u).1 (projected c v).1 := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  let f := ForwardOrderedProjections.frontierAt c.T c.cut u.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut v.1
  let a := projected c u
  let d := projected c v
  have hne : f.1 ≠ g.1 := by
    intro heq
    have hindices : u.1 = v.1 :=
      ForwardOrderedProjections.frontierAt_injective c.T c.cut
        (Subtype.ext heq)
    exact (ne_of_lt hij) hindices
  have hfg : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut u.1 v.1 hij
  exact ForwardProjectedTerminalOrder.ordered_frontier_projections_forwardAux
    c.T hc.1 c.hnon c.cut f.1 g.1 a.1 d.1
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut u.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut v.1)
    hne hfg a.2 d.2
    (projected_cone c u) (projected_cone c v)
    u.2.1.length v.2.1.length
    (projected_height c u) (projected_height c v)
    hlength

/-- The same cross-frontier hypothesis supplies the
ambient LENGTH inequality required for skew clause (ii).
Ranks are taken in T and never silently equated with
the ambient list lengths. -/
theorem projected_length_le_of_tail_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : LocalAddress c)
    (hij : u.1 < v.1)
    (hlength : u.2.1.length ≤ v.2.1.length) :
    (projected c u).1.length ≤ (projected c v).1.length := by
  rcases projected_forward_order_of_tail_length_le c u v hij hlength with
    hlt | ⟨heq, _⟩ <;> omega

end DualTree.ForwardQFinalProjectionOrder
