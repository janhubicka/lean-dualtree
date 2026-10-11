import DualTree.ForwardQExceptionalLowFrontier
import DualTree.ForwardQCutChildFrontierRank
import DualTree.ForwardQMarkerRankBand
import DualTree.ForwardQFrontierIndexOrder

/-!
# Exact rank-band matching for every actual corrected Q marked projection

The corrected literal marker set R has only two forms:
* the first forward-cut boundary of an exceptional old source terminal;
* a literal ambient child of the source's maximal interior cut.

All three source-facing marker cases now have exact ranks in both
the reconstructed Q support and the selected minimal frontier of the
enclosing complete support T. Their combination gives, for every
actual D₂ marked projection P_i with sorted frontier f_i,

  (h_Q(P_i), h_T(f_i)) =
    (h_S(cut), h_T(cut))
  OR
    (h_S(cut)+1, h_T(cut)+1).

In particular, comparison of Q-intrinsic ranks of any two selected
projected leaves is *equivalent* to comparison of their minimal
ambient T-frontier ranks, independently of their local D₂ tails.
This is the precise matching absent from the printed Lemma 27 proof.

No vector-one-complete/starred-domain assumption is used in this
geometric result. Word/colouring compatibility remains open.
-/

namespace DualTree.ForwardQFrontierBandMatch

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- Every genuine corrected D₂ projection belongs to exactly
the corresponding low or high source-cut / complete-frontier
rank band. The statement concerns the *actual* Q support,
not a surrogate signature skeleton. -/
theorem marked_Q_T_frontier_rank_band
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    (SkewTree.heightAt (nodes c x).toList
       (markedProjection c x i).1 =
         SkewTree.heightAt c.source.tree c.cut ∧
     SkewTree.heightAt c.T
       (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
         SkewTree.heightAt c.T c.cut) ∨
    (SkewTree.heightAt (nodes c x).toList
       (markedProjection c x i).1 =
         SkewTree.heightAt c.source.tree c.cut + 1 ∧
     SkewTree.heightAt c.T
       (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
         SkewTree.heightAt c.T c.cut + 1) := by
  classical
  let marker := ForwardQMeetClosed.markerOfBullet c i
  have hr : marker.1 ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout := marker.2
  have hfamilies :
      marker.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          c.source c.cut c.hout ++
        (SkewTree.allFin b).map (fun j => c.cut ++ [j]) := by
    simpa [ForwardStarredSignature.literalR] using hr
  have hmarkerIndex :
      ForwardQMarkerCoverage.bulletForMarker c marker = i :=
    ForwardQMeetClosed.bulletForMarker_markerOfBullet c i
  rcases List.mem_append.mp hfamilies with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        c.source c.cut c.hcut c.hmax c.hout
        marker.1 hterminal
    let terminalMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    have hmarker : marker = terminalMarker := by
      apply Subtype.ext
      exact ht.symm
    have hindex :
        ForwardQMarkerCoverage.bulletForMarker c terminalMarker = i := by
      rw [← hmarker]
      exact hmarkerIndex
    have hQ := ForwardQExceptionalRanks.exceptional_projection_Q_rank_eq_source
      c x t
    change SkewTree.heightAt (nodes c x).toList
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c terminalMarker)).1 =
      SkewTree.heightAt c.source.tree t.1 at hQ
    rw [hindex] at hQ
    rcases ForwardQExceptionalRanks.exceptional_source_rank_band
        hb c t.1 t.2 with htLow | htHigh
    · left
      have hT := ForwardQExceptionalLowFrontier.exceptional_low_frontier_T_rank
        c t htLow
      change SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut
          (ForwardQMarkerCoverage.bulletForMarker c terminalMarker).1).1 =
        SkewTree.heightAt c.T c.cut at hT
      rw [hindex] at hT
      exact ⟨hQ.trans htLow, hT⟩
    · right
      have hT := ForwardQExceptionalHighFrontier.exceptional_high_frontier_T_rank
        c t htHigh
      change SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut
          (ForwardQMarkerCoverage.bulletForMarker c terminalMarker).1).1 =
        SkewTree.heightAt c.T c.cut + 1 at hT
      rw [hindex] at hT
      exact ⟨hQ.trans htHigh, hT⟩
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hchild
    let childMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨c.cut ++ [j],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout j⟩
    have hmarker : marker = childMarker := by
      apply Subtype.ext
      exact hj.symm
    have hindex :
        ForwardQMarkerCoverage.bulletForMarker c childMarker = i := by
      rw [← hmarker]
      exact hmarkerIndex
    right
    have hQ := ForwardQCutChildRank.projected_cut_child_Q_height c x j
    change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 =
      SkewTree.heightAt c.source.tree c.cut + 1 at hQ
    rw [hindex] at hQ
    have hT := ForwardQCutChildFrontierRank.cut_child_frontier_T_rank c j
    change SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c childMarker).1).1 =
      SkewTree.heightAt c.T c.cut + 1 at hT
    rw [hindex] at hT
    exact ⟨hQ, hT⟩

/-- Strict comparison of intrinsic Q levels of two genuine
selected leaves is equivalent to strict comparison of the
intrinsic T levels of their selected frontier roots. -/
theorem Q_rank_lt_iff_frontier_T_rank_lt
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c)) :
    (SkewTree.heightAt (nodes c x).toList
      (markedProjection c x i).1 <
     SkewTree.heightAt (nodes c x).toList
      (markedProjection c x j).1) ↔
    (SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 <
     SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1) := by
  rcases marked_Q_T_frontier_rank_band hb c x i with hi | hi
  <;> rcases marked_Q_T_frontier_rank_band hb c x j with hj | hj
  <;> constructor <;> intro h <;> omega

/-- Equal intrinsic Q heights of two actual D₂ projected
leaves are equivalent to equal T heights of their minimal
frontier roots. -/
theorem Q_rank_eq_iff_frontier_T_rank_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c)) :
    (SkewTree.heightAt (nodes c x).toList
      (markedProjection c x i).1 =
     SkewTree.heightAt (nodes c x).toList
      (markedProjection c x j).1) ↔
    (SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
     SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1) := by
  rcases marked_Q_T_frontier_rank_band hb c x i with hi | hi
  <;> rcases marked_Q_T_frontier_rank_band hb c x j with hj | hj
  <;> constructor <;> intro h <;> omega

/-- In the genuine sorted D₂ coordinate order, the intrinsic
heights of the actual reconstructed marked Q leaves are
nondecreasing, independent of the selected local tails. -/
theorem Q_rank_mono_of_sorted_bullets
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x i).1 ≤
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x j).1 := by
  have hfront := ForwardQFrontierIndexOrder.frontier_T_rank_mono
    c i j hij
  rcases marked_Q_T_frontier_rank_band hb c x i with hi | hi
  <;> rcases marked_Q_T_frontier_rank_band hb c x j with hj | hj
  <;> omega

end DualTree.ForwardQFrontierBandMatch
