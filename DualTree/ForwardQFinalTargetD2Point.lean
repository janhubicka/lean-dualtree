import DualTree.ForwardQFinalUniqueTargetTerminals
import DualTree.ForwardQFinalTerminalD2Support
import DualTree.ForwardQFinalTerminalMarkerFrontier
import DualTree.ForwardQFinalSupportedTerminalSafety

/-!
# Select the exact target terminal's local D2 point for each R marker

Every original literal R marker r has a unique terminal of the
same-signature supported target O extending r. Such a terminal
belongs to the original complete T, lies after the actual maximal
cut, and belongs to the rank-filtered final support T'_M.

The verified unique safe-address decoder therefore gives a shortened
local point z, at the EXACT source D2 frontier bulletForMarker(r).
Since this is a late point of T'_M, the local z is an ACTUAL selected
variable root of the local mixed Ramsey component f_i.

This file selects that point and proves the two exact laws:
its corrected projection is the required target terminal, and it
belongs to the local component variable support.

No simultaneous D2 vector-one starred order or full Q starred
object equality is claimed. Those are the remaining geometric
and Ramsey constraints on the selected D2 tuple.
-/

namespace DualTree.ForwardQFinalTargetD2Point

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUniqueTargetTerminals

/-- A target tree inside the exact final rank-filtered support
lies inside the unchanged original complete T. -/
theorem targetTree_subset_complete_of_final_support
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) :
    ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T := by
  intro t ht
  exact ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
    g.core f (m + q) t (hSupport t ht)

/-- Every original literal source R marker has a genuine shortened
local point whose projection is EXACTLY its unique TARGET O terminal.
The same point belongs to the true variable support of component f_i. -/
theorem exists_target_D2_local_point_for_marker
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    ∃ z : BoundedNode b (k - (m + 1)),
      (projected g.core
        ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,z⟩).1 =
      (targetLeafForSourceMarker hb g O L
        (targetTree_subset_complete_of_final_support
          g f O hSupport) r).1 ∧
      z ∈ (f.vector.components
        (ForwardQMarkerCoverage.bulletForMarker g.core r).1).support := by
  let hT := targetTree_subset_complete_of_final_support
    g f O hSupport
  let leaf := targetLeafForSourceMarker hb g O L hT r
  have hprefix : IsPrefix r.1 leaf.1 :=
    targetLeafForSourceMarker_prefix hb g O L hT r
  have hafter : ¬ ForwardAux leaf.1 g.core.cut :=
    ForwardQFinalSupportedTerminalSafety.terminal_after_maximal_interior_cut
      hb O g.core.cut L.cutInterior L.cutMaximal
      leaf.1 leaf.2.1 leaf.2.2
  have hfinal :
      leaf.1 ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q) := hSupport leaf.1 leaf.2.1
  obtain ⟨a,hSafe⟩ :=
    ForwardQFinalSupportedTerminalSafety.final_support_after_cut_has_safe_address
      g.core f leaf.1 hfinal hafter
  rcases a with ⟨i,z⟩
  have hi : i =
      (ForwardQMarkerCoverage.bulletForMarker g.core r).1 :=
    ForwardQFinalTerminalMarkerFrontier.safe_address_frontier_eq_marker_index
      g.core r leaf.1 (hT leaf.1 leaf.2.1) hprefix
      ⟨i,z⟩ hSafe
  have hLocal :=
    ForwardQFinalTerminalD2Support.safe_address_local_support_of_final_support
      g.core f leaf.1 hfinal hafter i z hSafe
  have hProjected :
      (projected g.core (⟨i,z⟩ : LocalAddress g.core)).1 = leaf.1 :=
    ForwardQFinalSafeAddressLookup.safeAddress_spec
      g.core leaf.1 ⟨i,z⟩ hSafe
  refine ⟨z, ?_, ?_⟩
  · rw [← hi]
    exact hProjected
  · rw [← hi]
    exact hLocal.1

/-- Canonically select the unique target O leaf's actual D2 local
point in the ORIGINAL source marker's sorted frontier cone. -/
noncomputable def targetD2LocalPoint
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    BoundedNode b (k - (m + 1)) :=
  Classical.choose
    (exists_target_D2_local_point_for_marker hb g f O L hSupport r)

/-- The selected local D2 point projects EXACTLY to the target
terminal associated with the original literal R marker. -/
theorem targetD2LocalPoint_projection
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    (projected g.core
      ⟨(ForwardQMarkerCoverage.bulletForMarker g.core r).1,
        targetD2LocalPoint hb g f O L hSupport r⟩).1 =
    (targetLeafForSourceMarker hb g O L
      (targetTree_subset_complete_of_final_support
        g f O hSupport) r).1 :=
  (Classical.choose_spec
    (exists_target_D2_local_point_for_marker hb g f O L hSupport r)).1

/-- The same selected target D2 point is truly a variable root in
the local mixed Ramsey component at its literal source D2 index. -/
theorem targetD2LocalPoint_mem_component_support
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    targetD2LocalPoint hb g f O L hSupport r ∈
      (f.vector.components
        (ForwardQMarkerCoverage.bulletForMarker g.core r).1).support :=
  (Classical.choose_spec
    (exists_target_D2_local_point_for_marker hb g f O L hSupport r)).2

end DualTree.ForwardQFinalTargetD2Point
