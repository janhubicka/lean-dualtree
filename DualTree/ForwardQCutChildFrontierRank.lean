import DualTree.ForwardQCutChildRank
import DualTree.ForwardQMarkerCoverage
import DualTree.ForwardFrontierRanks
import DualTree.SupportHeightRanks

/-!
# Ambient complete-support frontier height for cut-child markers

The literal forward-corrected marker family includes every ambient
child cut ++ [i] of the last original interior node cut. Its selected
frontier in the complete ambient support T lies strictly below cut
in the prefix tree: it extends the literal child marker.

Every minimal T-frontier outside the forward-inclusive cut has
intrinsic T height either h_T(cut) or h_T(cut)+1. The strict
prefix relation therefore forces the second alternative.

This computes the actual T-frontier rank of the projected
cut-child family, independently of the local D₂ marked tail.
The result is an ingredient of a proposed two-band alignment
between intrinsic Q heights and ambient T-frontier heights.
Exceptional-source-terminal frontiers require a separate proof.
-/

namespace DualTree.ForwardQCutChildFrontierRank

open ForwardSourceQTree

/-- The minimal selected T frontier for an actual literal
cut-child marker has exactly one more intrinsic T predecessor
than the source cut, even if the ambient edge is stretched. -/
theorem cut_child_frontier_T_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Fin b) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨c.cut ++ [i],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout i⟩
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1).1 =
      SkewTree.heightAt c.T c.cut + 1 := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨c.cut ++ [i],
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i⟩
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut
    (ForwardQMarkerCoverage.bulletForMarker c marker).1).1
  change SkewTree.heightAt c.T f =
    SkewTree.heightAt c.T c.cut + 1
  have hfront : CutFrontier.Frontier c.T
      (fun u => ForwardAux u c.cut) f :=
    ForwardOrderedProjections.frontierAt_spec
      c.T c.cut (ForwardQMarkerCoverage.bulletForMarker c marker).1
  have hmarkerPrefix : IsPrefix (c.cut ++ [i]) f := by
    have hh :=
      (ForwardLiteralFrontierCoordinates.frontierFor_spec
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly marker).2
    rw [← ForwardQMarkerCoverage.bullet_frontier_eq_marker_frontier
      c marker] at hh
    exact hh
  have hcutChild : IsStrictPrefix c.cut (c.cut ++ [i]) := by
    refine ⟨⟨[i], rfl⟩, ?_⟩
    intro heq
    have hh := congrArg List.length heq
    simp at hh
  have hcutF : IsStrictPrefix c.cut f :=
    Lemma27QInterior.strictPrefix_trans_prefix
      hcutChild hmarkerPrefix
  have hrankLt : SkewTree.heightAt c.T c.cut <
      SkewTree.heightAt c.T f :=
    SupportHeightRanks.heightAt_lt_of_strictPrefix
      c.T c.hcutT hcutF
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hfrontBound : SkewTree.heightAt c.T f ≤
      SkewTree.heightAt c.T c.cut + 1 :=
    ForwardFrontierRanks.frontier_rank_le_cut_succ
      c.T hc.1 c.hnon c.cut f c.hcutT hfront
  omega

/-- The corresponding *actual* D₂ projected point has ambient
T-rank one above the cut, plus the length of its local tail. -/
theorem cut_child_projection_T_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : Fin b) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨c.cut ++ [i],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout i⟩
    SkewTree.heightAt c.T
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
      SkewTree.heightAt c.T c.cut + 1 +
        (x.bulletPoint
          (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨c.cut ++ [i],
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i⟩
  change SkewTree.heightAt c.T
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
      SkewTree.heightAt c.T c.cut + 1 +
        (x.bulletPoint
          (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length
  have hproj :=
    ForwardUniformConeDomains.projectCommon_height
      c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1)
      (ForwardOrderedProjections.frontierAt_spec
        c.T c.cut (ForwardQMarkerCoverage.bulletForMarker c marker).1)
      (x.bulletPoint
        (ForwardQMarkerCoverage.bulletForMarker c marker))
  have hfront := cut_child_frontier_T_rank c i
  change SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1).1 =
      SkewTree.heightAt c.T c.cut + 1 at hfront
  rw [hfront] at hproj
  exact hproj

end DualTree.ForwardQCutChildFrontierRank
