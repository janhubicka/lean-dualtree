import DualTree.ForwardQFinalTerminalMarkerFrontier
import DualTree.ForwardQFinalSelectedPredecessors

/-!
# Safe target-terminal points are actual local Ramsey variable roots

The genuine height-budgeted final support T'_M is the union of
inclusive-cut retained nodes and selected projections P_i(z) of
ACTUAL local component variable roots satisfying the final rank
budget.

Consequently, a root t of T'_M after the inclusive cut, whenever
its verified unique safe address is (i,z), has that precise tagged
address (i,z) in the selectedLocalRoots set. Thus z belongs to the
literal variable support of component f_i.

Together with the previously checked source-marker frontier
alignment, every terminal of a supported same-signature target O
corresponds to one original source D2 marker whose selected local
point is an ACTUAL local Ramsey word variable root, not an
arbitrary shortened cone point.

This is a support-membership statement only. Selecting these local
points in ALL D2 coordinates need not yet satisfy the corrected
vector-one starred order. The exact terminal reconstruction and
full Q-object equality remain open.
-/

namespace DualTree.ForwardQFinalTerminalD2Support

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalTerminalMarkerFrontier

/-- If an after-cut vertex lies in the exact final height-filtered
support and its actual safe address is a, then a is among the
selected local variable-root tags of the original mixed word f. -/
theorem safe_address_selected_local_root_of_final_support
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f (m + q))
    (hafter : ¬ ForwardAux t c.cut)
    (a : LocalAddress c)
    (hsafe : ForwardQFinalSafeAddressLookup.safeAddress c t = some a) :
    a ∈ selectedLocalRoots c f (m + q) := by
  classical
  have hselected : t ∈ selectedProjectedRoots c f (m + q) := by
    change t ∈ retained c ∪ selectedProjectedRoots c f (m + q) at ht
    rcases Finset.mem_union.mp ht with hret | hproj
    · exact False.elim (hafter (Finset.mem_filter.mp hret).2)
    · exact hproj
  obtain ⟨u, hu, hproj⟩ := Finset.mem_image.mp hselected
  have hSafeU :
      ForwardQFinalSafeAddressLookup.safeAddress c t = some u := by
    rw [← hproj]
    exact ForwardQFinalSafeAddressLookup.safeAddress_projected c u
  have heq : a = u := Option.some.inj (hsafe.symm.trans hSafeU)
  rw [heq]
  exact hu

/-- The local address selected for a late T'_M root really is
an ORIGINAL COMPONENT-VARIABLE ROOT z of f_i, with the prescribed
rank filter. It is not merely some short address inside cone i. -/
theorem safe_address_local_support_of_final_support
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f (m + q))
    (hafter : ¬ ForwardAux t c.cut)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hsafe : ForwardQFinalSafeAddressLookup.safeAddress c t =
      some (⟨i,z⟩ : LocalAddress c)) :
    z ∈ (f.vector.components i).support ∧
      FitsTargetHeight c f (m + q) (⟨i,z⟩ : LocalAddress c) := by
  have hselected :=
    safe_address_selected_local_root_of_final_support
      c f t ht hafter ⟨i,z⟩ hsafe
  obtain ⟨htag,hbudget⟩ :=
    (selectedLocalRoots_mem_iff c f (m + q) ⟨i,z⟩).1 hselected
  exact ⟨
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 htag,
    hbudget⟩

/-- Every terminal of a genuine target O inside the corrected final
T'_M support has a safely selected D2 coordinate r and a local
point z that belongs to the ACTUAL local Ramsey component support
at that exact source marker's index. -/
theorem supported_target_terminal_D2_point_in_local_support
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
      t ∈ finalBudgetSupport g.core f (m + q))
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ (r : ForwardSortedMixedProduct.Marker
        g.core.source g.core.cut g.core.hout)
      (z : BoundedNode b (k - (m + 1))),
      ForwardQFinalSafeAddressLookup.safeAddress
        g.core t =
          some (⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
            z⟩ : LocalAddress g.core) ∧
      z ∈ (f.vector.components
        (ForwardQMarkerCoverage.bulletForMarker g.core r).1).support := by
  obtain ⟨r,z,haddr⟩ :=
    supported_terminal_safe_address_at_original_marker
      hb g f O cutO H hSupport t ht hterminal
  have hafterO : ¬ ForwardAux t cutO :=
    ForwardQFinalSupportedTerminalSafety.terminal_after_maximal_interior_cut
      hb O cutO H.cutInterior H.cutMaximal
      t ht hterminal
  have hcut : cutO = g.core.cut :=
    ForwardQFinalFullSignature.complete_signature_forces_same_cut
      hb g O cutO H
  have hafter : ¬ ForwardAux t g.core.cut := by
    simpa only [hcut] using hafterO
  have hlocal :=
    safe_address_local_support_of_final_support
      g.core f t (hSupport t ht) hafter
      (ForwardQMarkerCoverage.bulletForMarker g.core r).1 z haddr
  exact ⟨r,z,haddr,hlocal.1⟩

end DualTree.ForwardQFinalTerminalD2Support
