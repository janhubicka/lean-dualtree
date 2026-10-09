import DualTree.BulletCoordinateRange

/-!
# Constructing mixed-product elements from distinguished marker points

For Lemma 27, a D₂ coordinate is attached to exactly one literal
signature marker. The previous module made the D₂ coordinate set
bijective with those markers. Consequently, once the word functions
in all d coordinates and a marked node for each literal marker are
provided, the mixed-product element is well typed without choosing
ambiguous preimages of D₂ indices.

This file makes this assembly explicit. It does not yet construct the
coordinate words from a starred tree-variable word, or prove that the
resulting Q is smooth-colouring compatible.
-/

namespace DualTree.MixedProduct

/-- Recover one marker responsible for a given distinguished bullet index. -/
noncomputable def markerOfBullet
    {d : Nat} {M : Type*} (index : M → Fin d)
    (i : BulletIndex (bulletKindOfRange index)) : M :=
  Classical.choose (bulletIndex_surjective index i)

/-- The recovered marker maps back to precisely the given bullet index. -/
theorem bulletIndex_markerOfBullet
    {d : Nat} {M : Type*} (index : M → Fin d)
    (i : BulletIndex (bulletKindOfRange index)) :
    bulletIndex index (markerOfBullet index i) = i :=
  Classical.choose_spec (bulletIndex_surjective index i)

/-- For an injective coordinate map, recovering a selected marker is exact. -/
theorem markerOfBullet_bulletIndex
    {d : Nat} {M : Type*} (index : M → Fin d)
    (hinj : Function.Injective index)
    (m : M) :
    markerOfBullet index (bulletIndex index m) = m := by
  apply bulletIndex_injective index hinj
  exact bulletIndex_markerOfBullet index (bulletIndex index m)

/-- Given all coordinate words and the nodes carried by the selected
markers, construct a complete mixed-product element with no D₁ slots. -/
noncomputable def elementFromMarkers
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (words : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n) :
    Element b n d α (bulletKindOfRange index) where
  words := words
  upPoint := fun i =>
    False.elim (bulletKindOfRange_ne_up index i.1 i.2)
  bulletPoint := fun i => point (markerOfBullet index i)

/-- Every original coordinate word survives the assembly unchanged. -/
theorem elementFromMarkers_words
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (words : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (i : Fin d) :
    (elementFromMarkers index words point).words i = words i := by
  rfl

/-- The node at the selected bullet coordinate is the node specified
for its unique marker. This is the essential indexing contract for Q. -/
theorem elementFromMarkers_bullet
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (hinj : Function.Injective index)
    (words : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (m : M) :
    (elementFromMarkers index words point).bulletPoint
        (bulletIndex index m) = point m := by
  change point (markerOfBullet index (bulletIndex index m)) = point m
  rw [markerOfBullet_bulletIndex index hinj m]

end DualTree.MixedProduct

namespace DualTree.LiteralMarkerMixedElement

/-- The type-correct element assembly at the actual D₂ coordinates
assigned to the literal R of Lemma 27. -/
noncomputable def assemble
    {b n l k : Nat} {α : Type*}
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
      TreeWord b n α)
    (point :
      {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout} →
        BoundedNode b n) :
    MixedProduct.Element b n
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel) :=
  MixedProduct.elementFromMarkers
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel)
    words point

/-- Each designated bullet coordinate recovers its original marked node. -/
theorem assemble_marker_point
    {b n l k : Nat} {α : Type*}
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
      TreeWord b n α)
    (point :
      {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout} →
        BoundedNode b n)
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

end DualTree.LiteralMarkerMixedElement
