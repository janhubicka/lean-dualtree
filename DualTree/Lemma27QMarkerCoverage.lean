import DualTree.Lemma27QTerminal
import DualTree.LiteralMarkerCoordinates

/-!
# Actual projected descendants of every literal R marker in Q

Lemma 27 uses the literal marker set R from Definition 26, not
the larger preliminary list of candidate cones. Its members are
terminal signature nodes and the immediate children of the cut.

This module proves that each genuine exceptional boundary and
each immediate child belongs to that literal R. It then shows
that the designated D₂ coordinate of any s ∈ R projects a
support node extending s, and that this node lies in the
reconstructed tree component S_w.

This is the marker-coverage ingredient for proving that
old interior vertices remain interior in S_w. No assertion
about the final starred word g_w is made here.
-/

namespace DualTree.Lemma27QMarkerCoverage

/-- Every ambient immediate child of the distinguished cut is
part of the literal R, by its second defining term. -/
theorem child_mem_literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (i : Fin b) :
    cut ++ [i] ∈ LiteralSignatureR.literalR O cut hout := by
  classical
  unfold LiteralSignatureR.literalR
  simp only [List.mem_dedup, List.mem_append]
  right
  exact List.mem_map.mpr
    ⟨i, DirectionalSupport.mem_allFin b i, rfl⟩

/-- Every exceptional signature boundary is among the literal
non-interior markers, once maximality of the cut is known. -/
theorem boundaryMarker_mem_literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SignatureMarker.boundaryMarkers O cut hout) :
    s ∈ LiteralSignatureR.literalR O cut hout := by
  classical
  have hSig : s ∈ StarredSignature.signatureTree O cut hout :=
    (LiteralSignatureR.mem_signatureTree_iff O cut hout s).2
      (Or.inr hs)
  have hNotCut : s ≠ cut := by
    intro heq
    have hNotBelow := SignatureInteriorExact.boundaryMarker_not_below_cut
      O cut hout hs
    subst s
    exact hNotBelow (isPrefix_refl cut)
  have hNotInt :
      s ∉ SkewTree.interior (StarredSignature.signatureTree O cut hout) := by
    intro hInt
    have hOriginal :=
      ((SignatureInteriorExact.signature_interior_iff_original_ne_cut
        O cut hcut hmax hout s).1 hInt).1
    have hEarly : PaperAux s cut := by
      simpa [SkewTree.paperAuxB] using hmax s hOriginal
    exact (InclusiveSignatureMarkers.boundaryMarker_paperCutBoundary
      O cut hout hs).1 hEarly
  unfold LiteralSignatureR.literalR
  simp only [List.mem_dedup, List.mem_append]
  left
  unfold LiteralSignatureR.signatureTerminalMarkers
  apply List.mem_filter.mpr
  refine ⟨hSig, ?_⟩
  simp [hNotInt, hNotCut]

/-- The marked support point in the uniquely assigned D₂
coordinate extends the literal marker which selected that coordinate. -/
theorem marker_prefix_projected_point
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
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    IsPrefix s.1
      (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcutT hlevel hm x
        (MixedProduct.bulletIndex
          (LiteralMarkerCoordinates.coordinate
            O cut hcut hmax hout T hcomplete hST hcutT hlevel) s)).1 := by
  let j := LiteralMarkerCoordinates.coordinate O cut hcut hmax
    hout T hcomplete hST hcutT hlevel s
  let i := MixedProduct.bulletIndex
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel) s
  have hfront :
      (Lemma27SignatureTree.frontierAt T cut j).1 =
      LiteralFrontierIndex.frontierFor
        O cut hcut hmax hout T hcomplete hST hcutT hlevel s := by
    simpa [Lemma27SignatureTree.frontierAt] using
      (LiteralMarkerCoordinates.coordinate_frontier
        O cut hcut hmax hout T hcomplete hST hcutT hlevel s)
  have hsfront :
      IsPrefix s.1 (Lemma27SignatureTree.frontierAt T cut i.1).1 := by
    change IsPrefix s.1 (Lemma27SignatureTree.frontierAt T cut j).1
    rw [hfront]
    exact (LiteralFrontierIndex.frontierFor_spec
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s).2
  have hfrontP :=
    Lemma27SignatureTree.markedProjection_frontier_prefix
      T hcomplete cut hcutT hlevel hm x i
  exact isPrefix_trans hsfront hfrontP

/-- Every literal R marker has a concrete projected support descendant
in S_w, rather than merely in the ambient support T. -/
theorem literalMarker_has_Q_descendant
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
    (s : Node b) (hs : s ∈ LiteralSignatureR.literalR O cut hout) :
    ∃ t : Node b,
      t ∈ Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x ∧
      IsPrefix s t := by
  let v : {r : Node b // r ∈ LiteralSignatureR.literalR O cut hout} := ⟨s, hs⟩
  let i := MixedProduct.bulletIndex
    (LiteralMarkerCoordinates.coordinate
      O cut hcut hmax hout T hcomplete hST hcutT hlevel) v
  let t := (Lemma27SignatureTree.markedProjection
    T hcomplete cut hcutT hlevel hm x i).1
  refine ⟨t, ?_, ?_⟩
  · exact Lemma27SignatureTree.signatureNodes_marked
      T hcomplete cut hcutT hlevel hm
      (Lemma27SignatureTree.oldSignatureBase O cut hout) x i
  · exact marker_prefix_projected_point
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x v

end DualTree.Lemma27QMarkerCoverage
