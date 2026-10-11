import DualTree.ForwardQExceptionalLex
import DualTree.ForwardQMarkerRankBand
import DualTree.ForwardQRetainedOrder

/-!
# All equal-intrinsic-rank old/new comparisons for corrected Q

The preceding results prove the geometry and source-rank formulas
for every actual projected D₂ marker, and show that an exceptional
source leaf at the final cut's intrinsic rank is projected to the
lexicographic right of every retained original interior vertex of
that rank.

This file combines the exact two-family literal marker
classification with those facts. If a retained old interior
point s and a new projected Q point P_i have equal intrinsic Q
heights, then the cut-child case is impossible (that case has
rank h_S(cut)+1); the exceptional leaf must have original
rank h_S(cut) and s must have that rank as well.
Therefore s <=lex P_i.

Because all old interior vertices have ambient length at most
all projected Q leaves, this settles both orientations of the
mixed old/new skew condition (ii), including the lex-reversed
case by antisymmetry. The strict different-rank comparisons and
the new/new pairs still require separate validation.
-/

namespace DualTree.ForwardQMixedCondII

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- Any old interior point and actual new projected D₂ point of
equal intrinsic Q rank are oriented old-to-new in ordinary
forward lex order. This is the exact mixed same-level
lexicographic statement needed by skew clause (ii). -/
theorem old_lex_marked_of_equal_Q_rank
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c))
    (heqQ : SkewTree.heightAt (nodes c x).toList s =
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1) :
    FinLexLE s (markedProjection c x i).1 := by
  classical
  let marker := ForwardQMeetClosed.markerOfBullet c i
  have hr : marker.1 ∈ ForwardStarredSignature.literalR
      c.source c.cut c.hout := marker.2
  have hfamilies :
      marker.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          c.source c.cut c.hout ++
        (SkewTree.allFin b).map (fun j => c.cut ++ [j]) := by
    simpa [ForwardStarredSignature.literalR] using hr
  have hi :
      ForwardQMarkerCoverage.bulletForMarker c marker = i :=
    ForwardQMeetClosed.bulletForMarker_markerOfBullet c i
  have hold :
      SkewTree.heightAt (nodes c x).toList s =
        SkewTree.heightAt c.source.tree s :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  have hbound :
      SkewTree.heightAt c.source.tree s ≤
        SkewTree.heightAt c.source.tree c.cut :=
    ForwardQOldCutChildOrder.old_interior_source_rank_le_cut
      c s hs
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
        hb c t.1 t.2 with htCut | htAbove
    · have hsCut :
          SkewTree.heightAt c.source.tree s =
            SkewTree.heightAt c.source.tree c.cut := by
        omega
      have hlex :=
        ForwardQExceptionalLex.old_top_rank_lex_exceptional_equal_rank_projection
          hb c x s hs hsCut t htCut
      change FinLexLE s
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c terminalMarker)).1 at hlex
      rw [← hmarker, hi] at hlex
      exact hlex
    · omega
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hchild
    let childMarker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨c.cut ++ [j],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout j⟩
    have hmarker : marker = childMarker := by
      apply Subtype.ext
      exact hj.symm
    have hchildRank := ForwardQCutChildRank.projected_cut_child_Q_height
      c x j
    change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 =
      SkewTree.heightAt c.source.tree c.cut + 1 at hchildRank
    have hsource :
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
        SkewTree.heightAt c.source.tree c.cut + 1 := by
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
              (ForwardQMarkerCoverage.bulletForMarker c childMarker)).1 := by
                rw [hmarker]
        _ = SkewTree.heightAt c.source.tree c.cut + 1 := hchildRank
    omega

/-- Skew clause (ii), old-to-new direction: equal-rank
lex-oriented old/new pairs have nondecreasing ambient length. -/
theorem old_to_marked_condII
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c))
    (_heq : SkewTree.heightAt (nodes c x).toList s =
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1)
    (_hlex : FinLexLE s (markedProjection c x i).1) :
    s.length ≤ (markedProjection c x i).1.length :=
  ForwardQRetainedOrder.Q_old_new_length_le c x s hs i

/-- Skew clause (ii), new-to-old direction: a reversed ordinary
lex comparison at an equal intrinsic Q rank is possible only
for equal nodes, hence implies the required length inequality. -/
theorem marked_to_old_condII
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c))
    (heq : SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 =
      SkewTree.heightAt (nodes c x).toList s)
    (hlex : FinLexLE (markedProjection c x i).1 s) :
    (markedProjection c x i).1.length ≤ s.length := by
  have hlexOld :=
    old_lex_marked_of_equal_Q_rank hb c x s hs i heq.symm
  have hsame : s = (markedProjection c x i).1 :=
    PaperAuxAntisymm.finLexLE_antisymm
      s (markedProjection c x i).1 hlexOld hlex
  simp [hsame]

end DualTree.ForwardQMixedCondII
