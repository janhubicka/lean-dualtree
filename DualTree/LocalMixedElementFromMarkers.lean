import DualTree.MixedElementFromMarkers

/-!
# Assembling literal-marker mixed elements at a separate local height

The existing LiteralMarkerMixedElement.assemble specializes the
mixed-product height to the ambient starred-word height n.
Lemma 27 needs an element at a possibly different local cone
height N = k - (m+1).  The marker index, however, depends only
on the starred tree, cut and complete support, not on N.

This typed constructor keeps those heights distinct and checks
the precise bullet-point coordinate contract without coercions.
-/

namespace DualTree.LocalMixedElementFromMarkers

/-- Assemble a mixed product whose local ambient height N is
independent of the ambient height n of the starred source word. -/
noncomputable def assemble
    {b n l k N : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (words : Fin (LiteralFrontierCount.frontiers T cut).length →
      TreeWord b N α)
    (point :
      {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout} →
        BoundedNode b N) :
    MixedProduct.Element b N
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel) :=
  MixedProduct.elementFromMarkers
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)
    words point

/-- The chosen local marked node appears unchanged at the
exact D₂ coordinate selected by the source marker injection. -/
theorem assemble_marker_point
    {b n l k N : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (words : Fin (LiteralFrontierCount.frontiers T cut).length →
      TreeWord b N α)
    (point :
      {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout} →
        BoundedNode b N)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    (assemble O cut hcut hmax hout T hcomplete hST hcutT
      hlevel words point).bulletPoint
      (MixedProduct.bulletIndex
        (LiteralMarkerCoordinates.coordinate
          O cut hcut hmax hout T hcomplete hST hcutT hlevel) s) =
      point s :=
  MixedProduct.elementFromMarkers_bullet
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)
    (LiteralMarkerCoordinates.coordinate_injective
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)
    words point s

end DualTree.LocalMixedElementFromMarkers
