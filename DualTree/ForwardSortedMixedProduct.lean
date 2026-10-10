import DualTree.ForwardSortedFrontiers
import DualTree.MixedElementFromMarkers

/-!
# The source's corrected literal D₀/D₂ mixed-product partition

The repaired Lemma 27 selects its bullet D₂ coordinates from the
*sorted* minimal frontiers beyond the inclusive forward cut.
Each member of the corrected literal marker list R receives exactly
one of these coordinates, and distinct markers have different
coordinates. All remaining coordinates belong to D₀. There are
no D₁ (up) coordinates in this particular construction.

This module packages that geometric coordinate map as an actual
MixedProduct.CoordKind function and then reconstructs a typed
mixed-product element from:
* one ordinary tree word at every sorted frontier coordinate; and
* one bounded local marked point for every literal marker.

The result really uses the forward-sorted coordinate map, rather
than the old printed-order mixed-product kind.

These typing results are prerequisites for the corrected Q tree
and colouring pullback. They do not imply that an arbitrary
mixed-product element belongs to the starred W_* subspace;
the vector 1-complete marked-point condition must be checked
separately.
-/

namespace DualTree.ForwardSortedMixedProduct

/-- The precise source-facing corrected literal marker type. -/
abbrev Marker
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t) :=
  {s : Node b // s ∈ ForwardLiteralFrontierCoordinates.R O cut hout}

/-- The corrected R → Fin d indexing map is a genuine
choice of sorted-frontier coordinates. -/
noncomputable def index
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Marker O cut hout →
      Fin (ForwardSortedFrontiers.frontiers T cut).length :=
  ForwardSortedFrontiers.coordinate
    O cut hcut hmax hout T hcomplete hnon hST hcutT hearly

/-- Exactly the selected literal R coordinates are bullet; all
other sorted frontier coordinates are plain. -/
noncomputable def kind
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Fin (ForwardSortedFrontiers.frontiers T cut).length →
      MixedProduct.CoordKind :=
  MixedProduct.bulletKindOfRange
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)

/-- Bullet membership is exactly membership in the range of
the genuine source marker coordinate map. -/
theorem kind_bullet_iff
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    kind O cut hcut hmax hout T hcomplete hnon hST hcutT hearly i =
      MixedProduct.CoordKind.bullet ↔
      ∃ s : Marker O cut hout,
        index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s = i := by
  exact MixedProduct.bulletKindOfRange_iff
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly) i

/-- No up-coordinate is introduced by the corrected D₀/D₂ split. -/
theorem kind_ne_up
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    kind O cut hcut hmax hout T hcomplete hnon hST hcutT hearly i ≠
      MixedProduct.CoordKind.up := by
  exact MixedProduct.bulletKindOfRange_ne_up
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly) i

/-- Literal corrected markers are bijective with the bullet indices. -/
theorem bulletIndex_bijective
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Function.Bijective
      (MixedProduct.bulletIndex
        (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)) := by
  exact MixedProduct.bulletIndex_bijective
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)
    (ForwardSortedFrontiers.coordinate_injective
      O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)

/-- Assemble an honest sorted D₀/D₂ mixed-product point from all
coordinate words and all corrected literal marked points. -/
noncomputable def assemble
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (words : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      TreeWord b (k - (m + 1)) α)
    (point : Marker O cut hout → BoundedNode b (k - (m + 1))) :
    MixedProduct.Element b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers T cut).length α
      (kind O cut hcut hmax hout T hcomplete hnon hST hcutT hearly) :=
  MixedProduct.elementFromMarkers
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)
    words point

/-- The corrected D₀/D₂ construction leaves all coordinate words
unchanged, including at the bullet coordinates. -/
theorem assemble_words
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (words : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      TreeWord b (k - (m + 1)) α)
    (point : Marker O cut hout → BoundedNode b (k - (m + 1)))
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    (assemble O cut hcut hmax hout T hcomplete hnon hST hcutT hearly
      words point).words i = words i := by
  rfl

/-- Each selected sorted frontier bullet coordinate returns
exactly the local marked point of its source literal R marker. -/
theorem assemble_marker_point
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (words : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      TreeWord b (k - (m + 1)) α)
    (point : Marker O cut hout → BoundedNode b (k - (m + 1)))
    (s : Marker O cut hout) :
    (assemble O cut hcut hmax hout T hcomplete hnon hST hcutT hearly
      words point).bulletPoint
      (MixedProduct.bulletIndex
        (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly) s) =
    point s := by
  exact MixedProduct.elementFromMarkers_bullet
    (index O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)
    (ForwardSortedFrontiers.coordinate_injective
      O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)
    words point s

end DualTree.ForwardSortedMixedProduct
