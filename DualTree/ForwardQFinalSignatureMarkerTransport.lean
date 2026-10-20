import DualTree.ForwardQFinalSupportedTerminalSafety
import DualTree.ForwardQFinalLiteralSignatureTree
import DualTree.ForwardSortedMixedProduct

/-!
# Identify the literal R markers under equal corrected signatures

The corrected complete signature compares the ACTUAL first-boundary
signature trees, not merely the old interior variable supports.
When two starred words have the same such signature at their common
maximal cut, their literal first-boundary marker lists R coincide.

Here this is proved using the existing exact signatureTree
equality and the actual definition of signatureTerminalMarkers
and literalR. The induced subtype equivalence fixes the underlying
homogeneous-tree marker exactly; it neither permutes markers nor
changes their forward-sorted ambient frontier index.

These facts are one prerequisite for attaching each requested target
terminal to the correct source D2 index. They do NOT yet select
target terminal coordinates, check their local mixed span membership
or establish full object-valued Q surjectivity.
-/

namespace DualTree.ForwardQFinalSignatureMarkerTransport

open ForwardSourceQTree
open ForwardQFinalLiteralSignatureTree

/-- Equality of actual literal forward signatures forces equality
of the entire corrected R marker lists, including boundary markers
and all ambient children of the common maximal interior cut. -/
theorem literalR_eq_of_same_literal_signature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O) :
    ForwardStarredSignature.literalR O g.core.cut
      (ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
        hb O g.core.cut H.cutInterior H.cutMaximal) =
    ForwardStarredSignature.literalR
      g.core.source g.core.cut g.core.hout := by
  let houtO :=
    ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
      hb O g.core.cut H.cutInterior H.cutMaximal
  have hsig :
      ForwardStarredSignature.signatureTree O g.core.cut houtO =
        ForwardStarredSignature.signatureTree
          g.core.source g.core.cut g.core.hout :=
    H.sameSignatureTree
  have hmarkers :
      ForwardStarredSignature.signatureTerminalMarkers
        O g.core.cut houtO =
      ForwardStarredSignature.signatureTerminalMarkers
        g.core.source g.core.cut g.core.hout := by
    simp only [ForwardStarredSignature.signatureTerminalMarkers]
    rw [hsig]
  unfold ForwardStarredSignature.literalR
  rw [hmarkers]

/-- Actual target literal-R marker subtypes correspond EXACTLY
to the original source's literal-R marker subtypes, by identical
raw nodes. This is a root-preserving equivalence, not an invented
enumeration or a global Hall assignment. -/
noncomputable def targetMarkerEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O) :
    {r : Node b // r ∈
      ForwardStarredSignature.literalR O g.core.cut
        (ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
          hb O g.core.cut H.cutInterior H.cutMaximal)} ≃
      ForwardSortedMixedProduct.Marker
        g.core.source g.core.cut g.core.hout := by
  let hr := literalR_eq_of_same_literal_signature hb g O H
  refine {
    toFun := fun r => ⟨r.1, by
      change r.1 ∈ ForwardStarredSignature.literalR
        g.core.source g.core.cut g.core.hout
      rw [← hr]
      exact r.2⟩
    invFun := fun r => ⟨r.1, by
      change r.1 ∈ ForwardStarredSignature.literalR O g.core.cut
        (ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
          hb O g.core.cut H.cutInterior H.cutMaximal)
      rw [hr]
      exact r.2⟩
    left_inv := by
      intro r
      apply Subtype.ext
      rfl
    right_inv := by
      intro r
      apply Subtype.ext
      rfl
  }

/-- Transporting a target marker to the source marker subtype
never changes its underlying actual ambient first-boundary node. -/
theorem targetMarkerEquiv_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (H : SameLiteralForwardSignature hb g O)
    (r : {t : Node b // t ∈
      ForwardStarredSignature.literalR O g.core.cut
        (ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
          hb O g.core.cut H.cutInterior H.cutMaximal)}) :
    (targetMarkerEquiv hb g O H r).1 = r.1 :=
  rfl

end DualTree.ForwardQFinalSignatureMarkerTransport
