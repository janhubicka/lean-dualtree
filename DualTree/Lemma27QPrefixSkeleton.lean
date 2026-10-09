import DualTree.Lemma27QLeafReplacement

/-!
# An explicit prefix-order embedding of the literal signature skeleton

The abstract leaf replacement is now made into an actual map of
typed node occurrences. An occurrence is either a vertex of the
old signature base Int(S') ∪ {t₀}, or a terminal marker in the
literal set R. The old embedding sends it to that original node;
the new embedding fixes the base and sends a marker to its
designated canonical D₂ projection.

All four combinations (base/base, base/marker, marker/base,
marker/marker) have now been checked for prefix preservation and
reflection. Since the two summands are disjoint, the original
map is injective, and therefore the Q map is also injective.

This verifies the *prefix geometry* of a leaf replacement.
It does not imply preservation of the printed auxiliary order,
ambient node lengths, skewness, or semi-completeness.
-/

namespace DualTree.Lemma27QPrefixSkeleton

/-- The literal pre-replacement signature occurrences. -/
abbrev Point
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :=
  Sum
    {u : Node b // u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout}
    {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}

/-- The original ambient label of a skeleton occurrence. -/
def originalNode
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    Point O cut hout → Node b
  | Sum.inl u => u.1
  | Sum.inr s => s.1

/-- The canonical reconstructed label of a skeleton occurrence. -/
noncomputable def newNode
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
    Point O cut hout → Node b
  | Sum.inl u => u.1
  | Sum.inr s =>
      (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1

/-- Original skeleton occurrences have distinct node labels.
The only nontrivial case is separation of the old base from R. -/
theorem originalNode_injective
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    Function.Injective (originalNode O cut hout) := by
  intro a b hab
  cases a with
  | inl u =>
      cases b with
      | inl v =>
          exact congrArg Sum.inl (Subtype.ext hab)
      | inr s =>
          have hEq : u.1 = s.1 := hab
          have hOld : s.1 ∈
              Lemma27SignatureTree.oldSignatureBase O cut hout := by
            simpa [hEq] using u.2
          exact False.elim
            ((Lemma27QLeafReplacement.literalMarker_not_oldBase
              O cut hcut hmax hout s) hOld)
  | inr s =>
      cases b with
      | inl u =>
          have hEq : s.1 = u.1 := hab
          have hOld : s.1 ∈
              Lemma27SignatureTree.oldSignatureBase O cut hout := by
            simpa [hEq] using u.2
          exact False.elim
            ((Lemma27QLeafReplacement.literalMarker_not_oldBase
              O cut hcut hmax hout s) hOld)
      | inr t =>
          exact congrArg Sum.inr (Subtype.ext hab)

/-- The canonical Q replacement preserves and reflects every prefix
relation of the two-sorted literal signature skeleton. -/
theorem newNode_prefix_iff_original
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
    (a c : Point O cut hout) :
    IsPrefix
      (newNode O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x a)
      (newNode O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x c)
      ↔ IsPrefix (originalNode O cut hout a)
          (originalNode O cut hout c) := by
  cases a with
  | inl u =>
      cases c with
      | inl v => rfl
      | inr s =>
          exact Lemma27QLeafReplacement.oldBase_prefix_projection_iff
            O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
            x u.1 u.2 s
  | inr s =>
      cases c with
      | inl u =>
          constructor
          · intro h
            exact False.elim
              ((Lemma27QLeafReplacement.projectedMarker_not_prefix_oldBase
                O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
                x u.1 u.2 s) h)
          · intro h
            have hBefore : PaperAux s.1 cut :=
              CutPreservation.paperAux_of_prefix h
                (SignatureInteriorExact.oldSignatureBase_before_cut
                  O cut hmax hout u.1 u.2)
            exact False.elim
              ((Lemma27QLeafReplacement.literalMarker_after_cut
                O cut hcut hmax hout s) hBefore)
      | inr t =>
          exact (Lemma27QLeafReplacement.projectedMarkers_prefix_iff
            O cut hcut hmax hout T hcomplete hST hcutT hlevel
            hm x s t).symm

/-- No two distinct literal skeleton occurrences have the same
reconstructed Q node. -/
theorem newNode_injective
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
    Function.Injective
      (newNode O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x) := by
  intro a c hac
  have hab : IsPrefix (originalNode O cut hout a)
      (originalNode O cut hout c) :=
    (newNode_prefix_iff_original O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x a c).1
      (by rw [hac]; exact isPrefix_refl _)
  have hba : IsPrefix (originalNode O cut hout c)
      (originalNode O cut hout a) :=
    (newNode_prefix_iff_original O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x c a).1
      (by rw [← hac]; exact isPrefix_refl _)
  exact originalNode_injective O cut hcut hmax hout
    (isPrefix_antisymm hab hba)

end DualTree.Lemma27QPrefixSkeleton
