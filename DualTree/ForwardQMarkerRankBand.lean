import DualTree.ForwardQCutChildRank
import DualTree.ForwardQMeetClosed

/-!
# Exact two-level rank band for all projected leaves of corrected Q

The literal corrected signature marker set R consists precisely of:
(1) terminal first-exit boundaries of exceptional old source leaves;
(2) all direct ambient children of the maximal original interior cut.

The two preceding modules prove:
* the Q replacement of an exceptional old source leaf has the
  same intrinsic height as that leaf, namely cut rank or cut rank+1;
* the Q replacement of every cut child has intrinsic height cut rank+1.

The sorted R -> D₂ correspondence is bijective, so every actual
D₂ bullet coordinate comes from exactly one of these markers.
This file combines the results into the exact source-facing theorem

  h_Q(P_i(s_i)) ∈ {h_S(cut), h_S(cut)+1}

for every Q projected terminal leaf, independent of the local
bullet-tail lengths and ambient complete-T ranks.

This is an intrinsic Q level theorem, not yet a proof of the
ambient word-length monotonicity required by skew clauses (ii)/(iii).
-/

namespace DualTree.ForwardQMarkerRankBand

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- Every actual forward-sorted D₂ projected leaf lies at the
intrinsic level of the final source cut or exactly one level above it. -/
theorem markedProjection_Q_rank_band
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 =
        SkewTree.heightAt c.source.tree c.cut ∨
    SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 =
        SkewTree.heightAt c.source.tree c.cut + 1 := by
  classical
  let marker := ForwardQMeetClosed.markerOfBullet c i
  have hr : marker.1 ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout := marker.2
  have hs :
      marker.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          c.source c.cut c.hout ++
        (SkewTree.allFin b).map (fun j => c.cut ++ [j]) := by
    simpa [ForwardStarredSignature.literalR] using hr
  have hi :
      ForwardQMarkerCoverage.bulletForMarker c marker = i :=
    ForwardQMeetClosed.bulletForMarker_markerOfBullet c i
  rcases List.mem_append.mp hs with hterminal | hchild
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
    have hsource :
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
          SkewTree.heightAt c.source.tree t.1 := by
      have hrank :=
        ForwardQExceptionalRanks.exceptional_projection_Q_rank_eq_source
          c x t
      change SkewTree.heightAt (nodes c x).toList
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c terminalMarker)).1 =
          SkewTree.heightAt c.source.tree t.1 at hrank
      calc
        SkewTree.heightAt (nodes c x).toList
            (markedProjection c x i).1 =
          SkewTree.heightAt (nodes c x).toList
            (markedProjection c x
              (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
                rw [hi]
        _ =
          SkewTree.heightAt (nodes c x).toList
            (markedProjection c x
              (ForwardQMarkerCoverage.bulletForMarker c terminalMarker)).1 := by
                rw [hmarker]
        _ = SkewTree.heightAt c.source.tree t.1 := hrank
    rcases ForwardQExceptionalRanks.exceptional_source_rank_band
        hb c t.1 t.2 with h | h
    · exact Or.inl (hsource.trans h)
    · exact Or.inr (hsource.trans h)
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hchild
    let childMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨c.cut ++ [j],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout j⟩
    have hmarker : marker = childMarker := by
      apply Subtype.ext
      exact hj.symm
    right
    have hrank := ForwardQCutChildRank.projected_cut_child_Q_height
      c x j
    change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 =
      SkewTree.heightAt c.source.tree c.cut + 1 at hrank
    calc
      SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x
            (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
              rw [hi]
      _ = SkewTree.heightAt (nodes c x).toList
            (markedProjection c x
              (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 := by
              rw [hmarker]
      _ = SkewTree.heightAt c.source.tree c.cut + 1 := hrank

end DualTree.ForwardQMarkerRankBand
