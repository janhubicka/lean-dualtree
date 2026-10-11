import DualTree.ForwardQExceptionalLength
import DualTree.ForwardQMarkerRankBand
import DualTree.ForwardQRetainedOrder
import DualTree.ForwardQMeetClosed

/-!
# Strict length for all Q markers at the next cut rank

Each genuinely projected D₂ marker of the repaired Q support has
intrinsic Q rank either h_S(cut) or h_S(cut)+1. Its literal source
marker is an exceptional-terminal first boundary or a direct
child of cut.

If a projected marker has Q rank h_S(cut)+1, then it is
strictly longer than cut in ambient word length:
* cut-child markers obviously extend cut++[j];
* exceptional markers have source terminal rank h_S(cut)+1,
  so the verified ancestor/cone-order boundary argument proves
  |cut|<|firstBoundary|<=|projected point|.

This is independent of local D₂ point lengths and source
support stretching. It is precisely the missing universal
strict mixed-rank inequality in the corrected Q construction.

The source-facing corollaries below discharge *both orientations*
of the mixed old/new skew clause (iii): an old interior vertex
strictly below a projected leaf's Q rank is strictly shorter;
the opposite strict rank orientation is impossible.
The new/new order inequalities and Q word/colouring remain open.
-/

namespace DualTree.ForwardQTopRankLength

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- Every genuine D₂ projection at intrinsic Q rank
h_S(cut)+1 has ambient word length strictly exceeding
that of the source cut. -/
theorem marked_projection_next_rank_strict_length
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c))
    (hnext :
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 =
      SkewTree.heightAt c.source.tree c.cut + 1) :
    c.cut.length < (markedProjection c x i).1.length := by
  classical
  let marker := ForwardQMeetClosed.markerOfBullet c i
  have hr : marker.1 ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout := marker.2
  have hfamilies :
      marker.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          c.source c.cut c.hout ++
        (SkewTree.allFin b).map (fun j => c.cut ++ [j]) := by
    simpa [ForwardStarredSignature.literalR] using hr
  have hindex :
      ForwardQMarkerCoverage.bulletForMarker c marker = i :=
    ForwardQMeetClosed.bulletForMarker_markerOfBullet c i
  rcases List.mem_append.mp hfamilies with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        c.source c.cut c.hcut c.hmax c.hout
        marker.1 hterminal
    let termMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    have hmarker : marker = termMarker := by
      apply Subtype.ext
      exact ht.symm
    have hidx : ForwardQMarkerCoverage.bulletForMarker
        c termMarker = i := by
      rw [← hmarker]
      exact hindex
    have hq :=
      ForwardQExceptionalRanks.exceptional_projection_Q_rank_eq_source
        c x t
    change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c termMarker)).1 =
      SkewTree.heightAt c.source.tree t.1 at hq
    rw [hidx] at hq
    have htRank :
        SkewTree.heightAt c.source.tree t.1 =
          SkewTree.heightAt c.source.tree c.cut + 1 := by
      omega
    have hstrict :=
      ForwardQExceptionalLength.exceptional_projection_strict_length
        c x t htRank
    change c.cut.length <
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c termMarker)).1.length at hstrict
    rwa [hidx] at hstrict
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hchild
    let childMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨c.cut ++ [j],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout j⟩
    have hmarker : marker = childMarker := by
      apply Subtype.ext
      exact hj.symm
    have hidx : ForwardQMarkerCoverage.bulletForMarker
        c childMarker = i := by
      rw [← hmarker]
      exact hindex
    have hpref : IsPrefix (c.cut ++ [j])
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 :=
      ForwardQMarkerCoverage.marker_prefix_projected_point
        c x childMarker
    have hlen := prefix_length_le hpref
    rw [hidx] at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    omega

/-- An old retained interior Q node of strictly smaller
intrinsic Q rank than any new projected D₂ leaf has strictly
smaller ambient word length. This discharges the mixed
old→new orientation of skew clause (iii). -/
theorem old_to_marked_condIII
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c))
    (hheight :
      SkewTree.heightAt (nodes c x).toList s <
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1) :
    s.length < (markedProjection c x i).1.length := by
  have hold :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  have hsForward : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hsourceSkew := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsourceSkew
  have hsSourceRankLe :
      SkewTree.heightAt c.source.tree s ≤
        SkewTree.heightAt c.source.tree c.cut :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.source.tree hsourceSkew.1
      (ForwardQRooted.source_nonsingleton c)
      (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
      hsForward
  by_cases hsmall :
      SkewTree.heightAt c.source.tree s <
        SkewTree.heightAt c.source.tree c.cut
  · have hbefore : s.length < c.cut.length :=
      SkewLevelOrder.length_lt_of_height_lt
        c.source.tree SkewTree.forwardAuxB hsourceSkew.1
        (ForwardQRooted.source_nonsingleton c)
        (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
        hsmall
    have hafter :=
      ForwardQRetainedOrder.Q_old_new_length_le c x c.cut c.hcut i
    omega
  · have hsEq :
        SkewTree.heightAt c.source.tree s =
          SkewTree.heightAt c.source.tree c.cut := by omega
    rcases ForwardQMarkerRankBand.markedProjection_Q_rank_band
        hb c x i with hnewEq | hnewNext
    · omega
    · have hlength :=
        marked_projection_next_rank_strict_length c x i hnewNext
      have hsLen : s.length ≤ c.cut.length := by
        rcases hsForward with hlt | ⟨heq, _⟩ <;> omega
      omega

/-- No new projected Q leaf can have strictly smaller Q rank
than a retained original interior vertex. Thus the reverse
new→old orientation of skew clause (iii) is vacuous. -/
theorem marked_to_old_condIII_impossible
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c)) :
    ¬ (SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 <
      SkewTree.heightAt (nodes c x).toList s) := by
  have hold :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  have hsForward : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hsourceSkew := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsourceSkew
  have hsSourceRankLe :
      SkewTree.heightAt c.source.tree s ≤
        SkewTree.heightAt c.source.tree c.cut :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.source.tree hsourceSkew.1
      (ForwardQRooted.source_nonsingleton c)
      (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
      hsForward
  rcases ForwardQMarkerRankBand.markedProjection_Q_rank_band
      hb c x i with hnewEq | hnewNext
  · omega
  · omega

end DualTree.ForwardQTopRankLength
