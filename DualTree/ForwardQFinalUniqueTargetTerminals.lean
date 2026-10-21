import DualTree.ForwardQFinalTerminalD2Support
import DualTree.ForwardSourceLeafMarkerEquiv
import DualTree.ForwardQFinalTargetTerminalMarker

/-!
# Unique requested target terminal for each ORIGINAL literal R marker

Given a target starred O with the same corrected literal signature
as the source and with all its tree vertices in the same complete
support T, O itself forms a genuine corrected source frame.

The existing canonical source-terminal/first-boundary-marker
correspondence can therefore be applied to O. Equality of literal
R markers transports its marker type back to the ORIGINAL source
without renaming underlying nodes.

Thus each original source R marker extends to exactly one terminal
of O. We choose that terminal and record the exact ambient prefix
incidence. This makes the target D2 marker-point selection canonical
up to the verified equalities, rather than an arbitrary terminal list
enumeration.

The chosen terminal still needs its shortened local inverse address
in the appropriate component variable support, and the collection
of those D2 points must satisfy the actual corrected starred order.
These independent obligations are not claimed here.
-/

namespace DualTree.ForwardQFinalUniqueTargetTerminals

open ForwardSourceQTree
open ForwardQFinalLiteralSignatureTree
open ForwardQFinalSignatureMarkerTransport

/-- Each source literal R marker r has ONE AND ONLY ONE target
terminal leaf extending r, under the true equal-signature and
common complete-support hypotheses. No order-preserving enumeration
or unrestricted marker injection is assumed. -/
theorem unique_target_terminal_for_source_marker
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    ∃! t : {t : Node b //
        t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree},
      IsPrefix r.1 t.1 := by
  let d := ForwardQFinalTargetTerminalMarker.targetFrame
    hb g O H hT
  let e := targetMarkerEquiv hb g O H
  let rr : ForwardSourceLeafMarkerEquiv.Marker d := e.symm r
  have hroot : rr.1 = r.1 := by
    calc
      rr.1 = (e rr).1 :=
        (targetMarkerEquiv_root hb g O H rr).symm
      _ = r.1 := congrArg Subtype.val (e.apply_symm_apply r)
  obtain ⟨leaf,hprefix⟩ :=
    ForwardSourceLeafMarkerEquiv.marker_has_source_leaf hb d rr
  refine ⟨leaf, ?_, ?_⟩
  · simpa only [hroot] using hprefix
  · intro leaf' hprefix'
    apply ForwardSourceLeafMarkerEquiv.marker_prefix_source_leaf_unique
      d rr leaf' leaf
    · simpa only [hroot] using hprefix'
    · exact hprefix

/-- The terminal chosen for each literal source R marker belongs to
the actual target O.tree and is noninterior by construction. -/
noncomputable def targetLeafForSourceMarker
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    {t : Node b // t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree} :=
  Classical.choose
    (unique_target_terminal_for_source_marker hb g O H hT r)

/-- The actual chosen target terminal extends the ORIGINAL literal
R node, not just some corresponding unnamed marker. -/
theorem targetLeafForSourceMarker_prefix
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    IsPrefix r.1
      (targetLeafForSourceMarker hb g O H hT r).1 :=
  (Classical.choose_spec
    (unique_target_terminal_for_source_marker hb g O H hT r)).1

/-- Complete-signature equality and containment in the exact final
rank-filtered support supply the same unique target-leaf
correspondence at every original source R marker. -/
theorem supported_unique_target_terminal_for_source_marker
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : ForwardQFinalRefinementRoots.LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout) :
    ∃! t : {t : Node b //
        t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree},
      IsPrefix r.1 t.1 := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  have hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T := by
    intro t ht
    exact ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
      g.core f (m + q) t (hSupport t ht)
  exact unique_target_terminal_for_source_marker hb g O L hT r

end DualTree.ForwardQFinalUniqueTargetTerminals
