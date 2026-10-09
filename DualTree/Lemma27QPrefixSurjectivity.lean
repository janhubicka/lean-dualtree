import DualTree.Lemma27QPrefixSkeleton

/-!
# Surjectivity of the prefix-preserving literal leaf replacement

The preceding module constructs an injective prefix-order embedding
on a disjoint union of old base nodes and literal terminal markers.
Here we verify that this typed encoding enumerates *all* nodes in
both finite skeletons, rather than an unnamed substructure.

The original nodes form the finite set Int(S') ∪ {t₀} ∪ R.
The reconstructed nodes form the actual S_w.
Surjectivity onto S_w uses the bijection between literal R and
bullet coordinates and is independent of the individual cone-word
letters.

Together with the prefix reflection theorem, this establishes a
genuine finite rooted prefix-poset isomorphism. It does not yet
imply the source's auxiliary-order skewness conditions.
-/

namespace DualTree.Lemma27QPrefixSurjectivity

/-- The original literal finite skeleton of Lemma 27. -/
noncomputable def originalSkeleton
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    Finset (Node b) := by
  classical
  exact (Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
    (LiteralSignatureR.literalR O cut hout).toFinset

/-- Every node in the literal old skeleton is the original
label of a typed old-base or marker occurrence. -/
theorem originalNode_surjective_on_skeleton
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (v : Node b) (hv : v ∈ originalSkeleton O cut hout) :
    ∃ p : Lemma27QPrefixSkeleton.Point O cut hout,
      Lemma27QPrefixSkeleton.originalNode O cut hout p = v := by
  classical
  unfold originalSkeleton at hv
  rcases Finset.mem_union.mp hv with hBase | hMarker
  · exact ⟨Sum.inl ⟨v, List.mem_toFinset.mp hBase⟩, rfl⟩
  · exact ⟨Sum.inr ⟨v, List.mem_toFinset.mp hMarker⟩, rfl⟩

/-- Every node in the reconstructed Q tree is the projected label
of a unique old-base or literal-marker occurrence. -/
theorem newNode_surjective_on_Q
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
    (v : Node b)
    (hv : v ∈ Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x) :
    ∃ p : Lemma27QPrefixSkeleton.Point O cut hout,
      Lemma27QPrefixSkeleton.newNode O cut hcut hmax hout
        T hcomplete hST hcutT hlevel hm x p = v := by
  classical
  change v ∈ Lemma27SignatureTree.signatureNodes
    T hcomplete cut hcutT hlevel hm
    (Lemma27SignatureTree.oldSignatureBase O cut hout) x at hv
  unfold Lemma27SignatureTree.signatureNodes at hv
  rcases Finset.mem_union.mp hv with hBase | hProj
  · exact ⟨Sum.inl ⟨v, List.mem_toFinset.mp hBase⟩, rfl⟩
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hProj
    let R := LiteralSignatureR.literalR O cut hout
    let index :
        {s : Node b // s ∈ R} →
          Fin (LiteralFrontierCount.frontiers T cut).length :=
      LiteralMarkerCoordinates.coordinate
        O cut hcut hmax hout T hcomplete hST hcutT hlevel
    obtain ⟨s, hjs⟩ := MixedProduct.bulletIndex_surjective index j
    refine ⟨Sum.inr s, ?_⟩
    change (Lemma27SignatureTree.markedProjection
      T hcomplete cut hcutT hlevel hm x
      (MixedProduct.bulletIndex index s)).1 = v
    rw [hjs]
    exact hj

/-- Source and target skeletons are both the ranges of the
corresponding occurrence maps, which are already injective. -/
theorem originalNode_mem_skeleton
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (p : Lemma27QPrefixSkeleton.Point O cut hout) :
    Lemma27QPrefixSkeleton.originalNode O cut hout p ∈
      originalSkeleton O cut hout := by
  classical
  cases p with
  | inl u =>
      unfold originalSkeleton
      exact Finset.mem_union.mpr
        (Or.inl (List.mem_toFinset.mpr u.2))
  | inr s =>
      unfold originalSkeleton
      exact Finset.mem_union.mpr
        (Or.inr (List.mem_toFinset.mpr s.2))

/-- Every typed occurrence of the Q replacement actually lies in
the reconstructed node set, not merely in the ambient support. -/
theorem newNode_mem_Q
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
    (p : Lemma27QPrefixSkeleton.Point O cut hout) :
    Lemma27QPrefixSkeleton.newNode
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x p ∈
      Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x := by
  cases p with
  | inl u =>
      exact Lemma27SignatureTree.signatureNodes_base
        T hcomplete cut hcutT hlevel hm
        (Lemma27SignatureTree.oldSignatureBase O cut hout) x u.1 u.2
  | inr s =>
      exact Lemma27SignatureTree.signatureNodes_marked
        T hcomplete cut hcutT hlevel hm
        (Lemma27SignatureTree.oldSignatureBase O cut hout) x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)

end DualTree.Lemma27QPrefixSurjectivity
