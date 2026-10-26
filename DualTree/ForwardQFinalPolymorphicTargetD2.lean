import DualTree.ForwardQFinalTargetD2Point
import DualTree.ForwardQFinalGlobalEnlargedWord

/-!
# Source-faithful target D₂ reconstruction with independent local alphabet

The original corrected exact-target D₂ theorem specialized the local
post-Ramsey mixed word to the SAME alphabet α as the ambient/source and
target. After extending the global final word to genuine enlarged
local words, that restriction is no longer appropriate.

All target-terminal geometry depends ONLY on the selected local
support, not on the type of local CONSTANT symbols. We now derive
the precise same-marker D₂ point existence and support membership
for an arbitrary local alphabet β (and in particular the genuine
enlarged alphabet α ⊕ Fin(m+1)), while the source and target remain
α-words.

This handles the geometric target-side part of the enlarged
Corollary-22 handoff without changing the source's literal marker
or the true corrected sorted frontier index. The simultaneous
D₂-starred order and complete Q word reconstruction for the newly
enlarged final interpolation remain separate proof steps.
-/

namespace DualTree.ForwardQFinalPolymorphicTargetD2

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUniqueTargetTerminals

/-- A target inside the TRUE rank-budgeted final support lies
in the original complete T, regardless of the alphabet β of
the actual local mixed Ramsey word. -/
theorem targetTree_subset_T
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) :
    ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T := by
  intro t ht
  exact ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
    g.core f (m + q) t (hSupport t ht)

/-- Every original literal R marker determines a genuine local D₂
support point whose canonical T projection is EXACTLY the unique
terminal of the target O above that marker. The proof holds for
an arbitrary local alphabet β and does not pretend that a local
auxiliary constant has already been evaluated in α. -/
theorem exists_target_D2_local_point_for_marker
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
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
        (targetTree_subset_T g f O hSupport) r).1 ∧
      z ∈ (f.vector.components
        (ForwardQMarkerCoverage.bulletForMarker g.core r).1).support := by
  let hT := targetTree_subset_T g f O hSupport
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

/-- A canonical target-selected local marker coordinate with
true support membership in the β-valued local Ramsey component. -/
noncomputable def targetD2LocalPoint
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
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

/-- The selected local point projects to the desired target
terminal, with exactly the original corrected marker index. -/
theorem targetD2LocalPoint_projection
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
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
      (targetTree_subset_T g f O hSupport) r).1 :=
  (Classical.choose_spec
    (exists_target_D2_local_point_for_marker
      hb g f O L hSupport r)).1

/-- The same point is a REAL β-valued local component variable
root: it is not a decoded alphabet constant or a fabricated D₂
index, even when β is the paper's enlarged constant alphabet. -/
theorem targetD2LocalPoint_mem_component_support
    {b n l k m q : Nat} {α β : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
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
    (exists_target_D2_local_point_for_marker
      hb g f O L hSupport r)).2

end DualTree.ForwardQFinalPolymorphicTargetD2
