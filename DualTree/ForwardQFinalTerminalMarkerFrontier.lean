import DualTree.ForwardQFinalTargetTerminalMarker
import DualTree.ForwardQFinalSupportedTerminalSafety
import DualTree.ForwardQMarkerCoverage
import DualTree.ForwardQFinalSafeAddressLookup

/-!
# Align target terminal R markers with their genuine safe frontier

For a corrected literal source R marker r and ANY genuine complete-T
node t extending r, the frontier selected for r also precedes t.
The proof uses the actual complete-support meet closure and the
inclusive-cut boundary of r: the common prefix of t and r's
selected frontier is a T vertex outside the cut, so minimality of
the selected frontier forces that common prefix to be the frontier.

As a consequence, whenever t has an actual safe projected address
(i,z), its sorted frontier index i is exactly the original source
D2 index bulletForMarker(r). No hypothetical new indexing or Hall
matching is used.

In particular every terminal of a target O with the same COMPLETE
corrected signature and O.tree within the true final support T'_M
admits a safely decoded tail at the correct source D2 frontier.

Local D2 support-membership, corrected starred ordering of THESE
tails, and equality of the complete target starred tree remain open.
-/

namespace DualTree.ForwardQFinalTerminalMarkerFrontier

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open DualTree.ForwardQFinalSupportedTerminalSafety

/-- The exact sorted source D2 frontier above an original literal
marker r is a prefix of EVERY complete-T node extending r.
This uses actual meet-closure and inclusive-cut geometry. -/
theorem marker_frontier_prefix_T_descendant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (t : Node b)
    (ht : t ∈ c.T)
    (hrt : IsPrefix r.1 t) :
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c r).1).1 t := by
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut
    (ForwardQMarkerCoverage.bulletForMarker c r).1).1
  have hf : CutFrontier.Frontier c.T
      (fun u => ForwardAux u c.cut) f :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut _
  have hrf : IsPrefix r.1 f := by
    change IsPrefix r.1
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c r).1).1
    rw [ForwardQMarkerCoverage.bullet_frontier_eq_marker_frontier c r]
    exact (ForwardLiteralFrontierCoordinates.frontierFor_spec
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly r).2
  have hboundary : ¬ ForwardAux r.1 c.cut :=
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r.1 r.2).1
  have hclosed : MeetGeometry.MeetClosed c.T :=
    ForwardInclusiveFrontier.meetClosed_complete_forward
      c.T c.hcomplete c.hnon
  let z := MeetGeometry.commonPrefix f t
  have hz : z ∈ c.T := hclosed f t hf.1 ht
  have hrz : IsPrefix r.1 z :=
    MeetGeometry.prefix_commonPrefix hrf hrt
  have hzOutside : ¬ ForwardAux z c.cut :=
    ForwardInclusiveFrontier.outside_of_prefix hboundary hrz
  have hzf : IsPrefix z f :=
    MeetGeometry.commonPrefix_prefix_left f t
  have hzEq : z = f := by
    by_contra hneq
    exact hzOutside (hf.2.2 z hz ⟨hzf,hneq⟩)
  change IsPrefix f t
  rw [← hzEq]
  exact MeetGeometry.commonPrefix_prefix_right f t

/-- The true sorted frontier index of a safe address for a
complete-support descendant t of marker r equals the original
source's selected D2 bullet index of r, on the nose. -/
theorem safe_address_frontier_eq_marker_index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout)
    (t : Node b)
    (ht : t ∈ c.T)
    (hrt : IsPrefix r.1 t)
    (a : LocalAddress c)
    (hsafe : ForwardQFinalSafeAddressLookup.safeAddress
      c t = some a) :
    a.1 = (ForwardQMarkerCoverage.bulletForMarker c r).1 := by
  have ha : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut a.1).1 t := by
    have hproject :=
      ForwardQFinalSafeAddressLookup.safeAddress_spec c t a hsafe
    rw [← hproject]
    exact ForwardQFinalRefinementRoots.projected_cone c a
  have hr : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c r).1).1 t :=
    marker_frontier_prefix_T_descendant c r t ht hrt
  have hEq :
      (ForwardOrderedProjections.frontierAt c.T c.cut a.1).1 =
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c r).1).1 :=
    CutFrontier.frontier_unique_above c.T
      (fun u => ForwardAux u c.cut)
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut a.1)
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c r).1)
      ha hr
  exact (ForwardOrderedProjections.frontierAt_injective c.T c.cut)
    (Subtype.ext hEq)

/-- Every terminal of a supported same-complete-signature target
has a safe shortened local tail at EXACTLY the selected D2
frontier index of an actual original literal R marker. -/
theorem supported_terminal_safe_address_at_original_marker
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ (r : ForwardSortedMixedProduct.Marker
        g.core.source g.core.cut g.core.hout)
      (z : BoundedNode b (k - (m + 1))),
      ForwardQFinalSafeAddressLookup.safeAddress
        g.core t =
          some (⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
            z⟩ : LocalAddress g.core) := by
  obtain ⟨r, hrt⟩ :=
    ForwardQFinalTargetTerminalMarker.supported_target_terminal_has_source_marker
      hb g f O cutO H hSupport t ht hterminal
  obtain ⟨a, hsafe⟩ :=
    supported_output_terminals_have_safe_addresses
      hb g f O cutO H hSupport t ht hterminal
  have htT : t ∈ g.core.T :=
    ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
      g.core f (m + q) t (hSupport t ht)
  rcases a with ⟨i,z⟩
  have hi : i =
      (ForwardQMarkerCoverage.bulletForMarker g.core r).1 :=
    safe_address_frontier_eq_marker_index
      g.core r t htT hrt ⟨i,z⟩ hsafe
  refine ⟨r,z,?_⟩
  rw [← hi]
  exact hsafe

end DualTree.ForwardQFinalTerminalMarkerFrontier
