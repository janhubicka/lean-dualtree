import DualTree.ForwardQFinalSignatureMarkerTransport
import DualTree.ForwardSourceLeafMarkerEquiv
import DualTree.ForwardQFinalHeightBudget

/-!
# Every supported target terminal has a literal SOURCE R marker

When a target starred word O has the same literal corrected
Definition-26 signature as the original source, its FIRST-BOUNDARY
marker list is literally identical to the original source R.

If O.tree is contained in the ambient complete-support T, we may
form a genuine source-facing Frame with O as its starred source,
the common maximal interior cut, and the SAME enclosing complete T.
The already checked canonical leaf/marker correspondence then
supplies an R marker below each O terminal. The exact marker subtype
equivalence transports it to the ORIGINAL source R without changing
its raw ambient node.

In particular every supported target terminal has a source marker
prefix even when it is not itself one of the source's terminals.
This is necessary for reconstructing the correct selected D2 index.

No local D2 tail membership or order is assumed here; those remain
distinct geometric and Ramsey-span obligations.
-/

namespace DualTree.ForwardQFinalTargetTerminalMarker

open ForwardSourceQTree
open ForwardQFinalLiteralSignatureTree
open ForwardQFinalSignatureMarkerTransport

/-- Reinterpret a supported target O as a legitimate corrected
forward-source frame inside exactly the original complete support T.
All source, cut and completeness hypotheses are verified directly. -/
noncomputable def targetFrame
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T) :
    Frame b n l k m α where
  source := O
  cut := g.core.cut
  hcut := H.cutInterior
  hmax := H.cutMaximal
  hout :=
    ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
      hb O g.core.cut H.cutInterior H.cutMaximal
  T := g.core.T
  hcomplete := g.core.hcomplete
  hnon := g.core.hnon
  hST := hT
  hcutT := g.core.hcutT
  hearly := g.core.hearly
  hm := g.core.hm

/-- Every ACTUAL target terminal in the same complete support
extends one of the ORIGINAL source's literal R markers. The target
and source markers have identical ambient nodes by the verified
same-signature equivalence; no arbitrary reassignment is made. -/
theorem target_terminal_has_source_marker
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (hT : ∀ t : Node b, t ∈ O.tree → t ∈ g.core.T)
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout,
      IsPrefix r.1 t := by
  let d := targetFrame hb g O H hT
  let leaf : ForwardSourceLeafMarkerEquiv.SourceLeaf d :=
    ⟨t, ⟨ht, hterminal⟩⟩
  obtain ⟨r, hprefix⟩ :=
    ForwardSourceLeafMarkerEquiv.source_leaf_has_marker d leaf
  let rt : {s : Node b // s ∈
      ForwardStarredSignature.literalR O g.core.cut
        (ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
          hb O g.core.cut H.cutInterior H.cutMaximal)} :=
    ⟨r.1, r.2⟩
  exact ⟨targetMarkerEquiv hb g O H rt, hprefix⟩

/-- In the actual rank-filtered final-support target class,
same COMPLETE corrected signatures and support containment
suffice to associate every output terminal with a LITERAL
original R marker. This is the needed domain for the selected
source D2 frontier-index map. -/
theorem supported_target_terminal_has_source_marker
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : ForwardQFinalRefinementRoots.LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport g.core f (m + q))
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout,
      IsPrefix r.1 t := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  have hT : ∀ u : Node b, u ∈ O.tree → u ∈ g.core.T := by
    intro u hu
    exact ForwardQFinalHeightBudget.finalBudgetSupport_subset_T
      g.core f (m + q) u (hSupport u hu)
  exact target_terminal_has_source_marker
    hb g O L hT t ht hterminal

end DualTree.ForwardQFinalTargetTerminalMarker
