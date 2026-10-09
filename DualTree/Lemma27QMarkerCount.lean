import DualTree.Lemma27QTreeCount
import DualTree.MixedElementFromMarkers
import Mathlib

/-!
# Counting exactly the D₂ coordinates of Lemma 27

The literal marker set R is a duplicate-free finite list. Each marker
has a unique frontier coordinate, and the selected D₂ coordinate type
is exactly the range of that injection.

Using the two finite equivalences
    Fin |R| ≃ {s // s ∈ R} ≃ D₂
we prove |D₂|=|R|. Consequently the already formalized cardinality
|S_w|=l+|D₂| sharpens to the literal source-facing formula
    |S_w|=l+|R|.

This establishes the exact count of the tree *nodes*, not yet its
interior, semi-complete branching or the word part g_w of Q.
-/

namespace DualTree.Lemma27QMarkerCount

/-- The actual bullet-coordinate type has cardinality exactly equal
to the number of distinct markers in the literal signature set R. -/
theorem bullet_card_eq_literalR_length
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
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    Fintype.card (MixedProduct.BulletIndex
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) =
    (LiteralSignatureR.literalR O cut hout).length := by
  classical
  let R := LiteralSignatureR.literalR O cut hout
  let M : Type := {s : Node b // s ∈ R}
  let d := (LiteralFrontierCount.frontiers T cut).length
  let index : M → Fin d :=
    LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
  let kind := LiteralMarkerProductKind.kind
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
  have hR : R.Nodup :=
    LiteralFrontierCount.literalR_nodup O cut hout
  let e : Fin R.length ≃ M := List.Nodup.getEquiv R hR
  letI : Fintype M := Fintype.ofEquiv (Fin R.length) e
  have hBij : Function.Bijective (MixedProduct.bulletIndex index) :=
    LiteralMarkerProductKind.literalMarker_bullet_bijective
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
  let eBullet : M ≃ MixedProduct.BulletIndex kind :=
    Equiv.ofBijective (MixedProduct.bulletIndex index) hBij
  calc
    Fintype.card (MixedProduct.BulletIndex kind) =
        Fintype.card M := Fintype.card_congr eBullet.symm
    _ = Fintype.card (Fin R.length) := Fintype.card_congr e.symm
    _ = R.length := by simp

/-- Exact source-facing cardinality of the tree skeleton of Q:
the l original interior nodes and one new node for each literal
marker, with no collisions or accidental extra nodes. -/
theorem sourceSignatureNodes_card_eq_l_add_literalR
    {b n l k m : Nat} {α : Type*}
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
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    (Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).card =
      l + (LiteralSignatureR.literalR O cut hout).length := by
  rw [Lemma27QTreeCount.sourceSignatureNodes_card
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x]
  rw [bullet_card_eq_literalR_length
    O cut hcut hmax hout T hcomplete hST hcutT hlevel]

end DualTree.Lemma27QMarkerCount
