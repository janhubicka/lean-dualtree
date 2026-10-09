import DualTree.Lemma27QInterior

/-!
# Prefix geometry of replacing literal R leaves by projected nodes

Lemma 27 retains the old interior base and replaces each literal
signature marker by a node in its uniquely assigned complete-skew
frontier cone. The previous development proves that every literal
marker has an assigned projected descendant and that the latter
are pairwise prefix-incomparable.

We show that all prefix relations between the old base and the
literal markers survive this replacement. Together with the
prefix antichain property of literal R, this gives a rooted
prefix-order embedding of the old signature skeleton into the
Q node set.

This does not imply that the ambient auxiliary order is preserved,
nor that the reconstructed node set satisfies the skew/semicomplete
axioms: both require additional geometry.
-/

namespace DualTree.Lemma27QLeafReplacement

/-- Literal markers are strictly outside the inclusive cut. -/
theorem literalMarker_after_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    ¬ PaperAux s.1 cut := by
  have hpersist :=
    SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout
  have hcone :=
    LiteralSignatureR.literalR_subset_coneMarkers
      O cut hout hpersist s.2
  exact (InclusiveSignatureMarkers.coneMarker_paperCutBoundary
    O cut hout hcone).1

/-- A literal marker cannot itself belong to the retained old base. -/
theorem literalMarker_not_oldBase
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    s.1 ∉ Lemma27SignatureTree.oldSignatureBase O cut hout := by
  intro hOld
  exact (literalMarker_after_cut O cut hcut hmax hout s)
    (SignatureInteriorExact.oldSignatureBase_before_cut
      O cut hmax hout s.1 hOld)

/-- The literal R is an antichain of source-prefix nodes. -/
theorem literalMarkers_prefix_implies_eq
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s t : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout})
    (hst : IsPrefix s.1 t.1) :
    s = t := by
  have hpersist :=
    SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout
  apply Subtype.ext
  exact LiteralSignatureR.literalR_unique_marker_in_cone
    O cut hout hpersist s.2 t.2 hst (isPrefix_refl t.1)

/-- Prefix comparability between a retained base vertex and a
new projected marker is the same as with its original literal marker. -/
theorem oldBase_prefix_projection_iff
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
    (u : Node b)
    (hu : u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    IsPrefix u
      (Lemma27SignatureTree.markedProjection T hcomplete cut
        hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1
      ↔ IsPrefix u s.1 := by
  have hmarker :
      IsPrefix s.1
        (Lemma27SignatureTree.markedProjection T hcomplete cut
          hcutT hlevel hm x
          (MixedProduct.bulletIndex
            (LiteralMarkerCoordinates.coordinate
              O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1 :=
    Lemma27QMarkerCoverage.marker_prefix_projected_point
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s
  have hbase : PaperAux u cut :=
    SignatureInteriorExact.oldSignatureBase_before_cut
      O cut hmax hout u hu
  constructor
  · intro hproj
    rcases le_total u.length s.1.length with hle | hle
    · exact CutFrontier.prefix_of_prefix_length_le hproj hmarker hle
    · have hmarkU : IsPrefix s.1 u :=
        CutFrontier.prefix_of_prefix_length_le hmarker hproj hle
      have hEarly : PaperAux s.1 cut :=
        CutPreservation.paperAux_of_prefix hmarkU hbase
      exact False.elim
        ((literalMarker_after_cut O cut hcut hmax hout s) hEarly)
  · intro hpre
    exact isPrefix_trans hpre hmarker

/-- A projected leaf cannot be a prefix of any old base point. -/
theorem projectedMarker_not_prefix_oldBase
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
    (u : Node b) (hu : u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    ¬ IsPrefix
      (Lemma27SignatureTree.markedProjection T hcomplete cut
        hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1
      u := by
  intro h
  have hEarly : PaperAux
      (Lemma27SignatureTree.markedProjection T hcomplete cut
        hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1 cut :=
    CutPreservation.paperAux_of_prefix h
      (SignatureInteriorExact.oldSignatureBase_before_cut O cut hmax hout u hu)
  exact Lemma27MarkedLeafGeometry.markedProjection_after_cut
    T hcomplete cut hcutT hlevel hm x
    (MixedProduct.bulletIndex
      (LiteralMarkerCoordinates.coordinate
        O cut hcut hmax hout T hcomplete hST hcutT hlevel) s) hEarly

/-- Prefix comparability of new projected marker points matches exactly
that of their old literal R markers: both mean equality of markers. -/
theorem projectedMarkers_prefix_iff
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
    (s t : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    IsPrefix s.1 t.1 ↔
      IsPrefix
        (Lemma27SignatureTree.markedProjection
          T hcomplete cut hcutT hlevel hm x
          (MixedProduct.bulletIndex
            (LiteralMarkerCoordinates.coordinate
              O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1
        (Lemma27SignatureTree.markedProjection
          T hcomplete cut hcutT hlevel hm x
          (MixedProduct.bulletIndex
            (LiteralMarkerCoordinates.coordinate
              O cut hcut hmax hout T hcomplete hST hcutT hlevel) t)).1 := by
  constructor
  · intro hst
    have hEq := literalMarkers_prefix_implies_eq
      O cut hcut hmax hout s t hst
    subst t
    exact isPrefix_refl _
  · intro hp
    have heqBullet :=
      Lemma27MarkedLeafGeometry.markedProjection_prefix_implies_same_index
        T hcomplete cut hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) t) hp
    have heqCoordinate :
        LiteralMarkerCoordinates.coordinate
          O cut hcut hmax hout T hcomplete hST hcutT hlevel s =
        LiteralMarkerCoordinates.coordinate
          O cut hcut hmax hout T hcomplete hST hcutT hlevel t :=
      congrArg Subtype.val heqBullet
    have hEq : s = t :=
      (LiteralMarkerCoordinates.coordinate_injective
        O cut hcut hmax hout T hcomplete hST hcutT hlevel) heqCoordinate
    subst t
    exact isPrefix_refl _

end DualTree.Lemma27QLeafReplacement
