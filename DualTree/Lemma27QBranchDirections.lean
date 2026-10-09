import DualTree.Lemma27QLeafReplacement

/-!
# Directional cone preservation under the Lemma 27 leaf replacement

The prefix-order equivalence between a literal marker s and its new
projection P(s) is not yet enough for the semi-complete branching
axioms: those also distinguish the b ambient directions below each
old interior node u.

We prove that replacement of a leaf by any extension cannot change
the first ambient direction seen from a proper prefix u of that leaf.
For the actual Q reconstruction, all old base nodes lie at or before
the cut while literal markers lie after it, so any base vertex that
precedes a marker precedes it *strictly*.

The resulting source-facing theorem preserves every b-direction
successor cone of an old base vertex. It does not on its own assert
that all these cones are occupied.
-/

namespace DualTree.Lemma27QBranchDirections

/-- Extending a terminal marker cannot change the first direction
observed from any of its proper prefixes. -/
theorem childCone_prefix_iff_of_strict_prefix
    {b : Nat} {u s t : Node b} (i : Fin b)
    (hus : IsStrictPrefix u s) (hst : IsPrefix s t) :
    IsPrefix (u ++ [i]) t ↔ IsPrefix (u ++ [i]) s := by
  constructor
  · intro h
    have huLen : u.length < s.length :=
      MeetClosedFromBranching.length_lt_of_strictPrefix hus
    have hchildLen : (u ++ [i]).length ≤ s.length := by
      simp only [List.length_append, List.length_singleton]
      omega
    exact CutFrontier.prefix_of_prefix_length_le h hst hchildLen
  · intro h
    exact isPrefix_trans h hst

/-- Every ambient first-direction cone from an old base vertex has
the same relation to its designated marker before and after Q. -/
theorem oldBase_childCone_prefix_iff
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
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout})
    (i : Fin b) :
    IsPrefix (u ++ [i])
      (Lemma27SignatureTree.markedProjection T hcomplete cut
        hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1
      ↔ IsPrefix (u ++ [i]) s.1 := by
  let p :=
    (Lemma27SignatureTree.markedProjection T hcomplete cut
      hcutT hlevel hm x
      (MixedProduct.bulletIndex
        (LiteralMarkerCoordinates.coordinate
          O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1
  have hsp : IsPrefix s.1 p :=
    Lemma27QMarkerCoverage.marker_prefix_projected_point
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s
  constructor
  · intro hchildP
    have huChild : IsPrefix u (u ++ [i]) := ⟨[i], rfl⟩
    have huP : IsPrefix u p :=
      isPrefix_trans huChild hchildP
    have huS : IsPrefix u s.1 :=
      (Lemma27QLeafReplacement.oldBase_prefix_projection_iff
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
        x u hu s).1 huP
    have hne : u ≠ s.1 := by
      intro heq
      have hsOld : s.1 ∈ Lemma27SignatureTree.oldSignatureBase
          O cut hout := heq ▸ hu
      exact (Lemma27QLeafReplacement.literalMarker_not_oldBase
        O cut hcut hmax hout s) hsOld
    exact (childCone_prefix_iff_of_strict_prefix i ⟨huS, hne⟩ hsp).1
      hchildP
  · intro hchildS
    exact isPrefix_trans hchildS hsp

end DualTree.Lemma27QBranchDirections
