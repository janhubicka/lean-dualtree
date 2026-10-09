import DualTree.Lemma27MarkedLeafGeometry
import DualTree.SignatureInteriorExact
import Mathlib

/-!
# Actual size and support containment of the Lemma 27 tree skeleton

The marked-leaf separation argument previously required the old
signature base to be at or before the cut. The exact signature
interior computation now proves this property.

Moreover, Int(S') ∪ {t₀} is precisely Int(S), as a *set*, and
therefore has exactly l members (not just at most l).
We combine this with the proved disjointness and injectivity of
the newly marked cone points to obtain the exact size of the
tree-component of Q, without a conditional old-base hypothesis.

All constructed vertices also belong to the old complete skew
support T. These facts do not, on their own, prove that S_w is
semi-complete or identify its interior inside the *new* tree.
-/

namespace DualTree.Lemma27QTreeCount

/-- The old signature base is precisely the original set of
interior support vertices. -/
theorem oldBase_mem_iff_original_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : Node b) :
    s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout ↔
      s ∈ SkewTree.interior O.tree := by
  change
    s ∈ SkewTree.interior
      (StarredSignature.signatureTree O cut hout) ++ [cut] ↔
    s ∈ SkewTree.interior O.tree
  rw [List.mem_append]
  simp only [List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact ((SignatureInteriorExact.signature_interior_iff_original_ne_cut
        O cut hcut hmax hout s).1 h).1
    · subst s
      exact hcut
  · intro hs
    by_cases heq : s = cut
    · exact Or.inr heq
    · exact Or.inl
        ((SignatureInteriorExact.signature_interior_iff_original_ne_cut
          O cut hcut hmax hout s).2 ⟨hs, heq⟩)

/-- Equality of the finite sets eliminates possible repetitions
from the original list presentation of the old signature base. -/
theorem oldBase_finset_eq_original_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset =
      (SkewTree.interior O.tree).toFinset := by
  classical
  ext s
  simp only [List.mem_toFinset]
  exact oldBase_mem_iff_original_interior O cut hcut hmax hout s

/-- The old signature base has precisely the l original
interior nodes, counted without repetitions. -/
theorem oldBase_card
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset.card =
      l := by
  classical
  have hsemi := O.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have hskew := hsemi.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hndTree : O.tree.Nodup := by
    simpa using hskew.1
  have hndInterior : (SkewTree.interior O.tree).Nodup := by
    unfold SkewTree.interior
    exact hndTree.filter _
  rw [oldBase_finset_eq_original_interior O cut hcut hmax hout]
  rw [List.toFinset_card_of_nodup hndInterior]
  exact O.interior_card

/-- Every vertex of the fixed old part already belongs to
the original complete support T. -/
theorem oldBase_subset_support
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (s : Node b)
    (hs : s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout) :
    s ∈ T := by
  have hsInterior :=
    (oldBase_mem_iff_original_interior O cut hcut hmax hout s).1 hs
  have hsTree : s ∈ O.tree := by
    unfold SkewTree.interior at hsInterior
    exact (List.mem_filter.mp hsInterior).1
  exact hST s hsTree

/-- The exact tree skeleton S_w is a subset of the complete
support T, with no extra external ambient nodes. -/
theorem sourceSignatureNodes_subset_support
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
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b)
    (hs : s ∈ Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x) :
    s ∈ T := by
  classical
  unfold Lemma27SignatureTree.sourceSignatureNodes
    Lemma27SignatureTree.signatureNodes at hs
  rcases Finset.mem_union.mp hs with hbase | hmark
  · exact oldBase_subset_support O cut hcut hmax hout T hST s
      (List.mem_toFinset.mp hbase)
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmark
    exact (Lemma27SignatureTree.markedProjection
      T hcomplete cut hcutT hlevel hm x i).2

/-- The precise cardinality of S_w: each of the l old interior
points is retained, and each D₂ coordinate supplies one new point. -/
theorem sourceSignatureNodes_card
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
    l + Fintype.card (MixedProduct.BulletIndex
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) := by
  have h := Lemma27MarkedLeafGeometry.signatureNodes_card_of_base_early
    T hcomplete cut hcutT hlevel hm
    (Lemma27SignatureTree.oldSignatureBase O cut hout)
    (SignatureInteriorExact.oldSignatureBase_before_cut O cut hmax hout) x
  change
    (Lemma27SignatureTree.sourceSignatureNodes O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x).card =
    (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset.card +
      Fintype.card (MixedProduct.BulletIndex
        (LiteralMarkerProductKind.kind
          O cut hcut hmax hout T hcomplete hST hcutT hlevel)) at h
  rw [oldBase_card O cut hcut hmax hout] at h
  exact h

end DualTree.Lemma27QTreeCount
