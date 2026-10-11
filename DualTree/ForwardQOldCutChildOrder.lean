import DualTree.ForwardQCutChildRank
import DualTree.ForwardQMarkerRankBand
import DualTree.ForwardQRetainedOrder
import DualTree.ForwardFrontierRanks
import DualTree.ForwardQMarkerCoverage

/-!
# Strict mixed old/new comparisons for projected cut-child markers

The corrected Q support retains the original source interior and
projects one marked leaf above every literal cut-child marker
`cut ++ [i]`. This special marker family admits strictly stronger
order statements than the previously proved general old/new
forward-auxiliary length monotonicity:

* the source intrinsic rank of any retained interior node is at
  most the source rank of the maximal cut;
* the ambient length of any retained interior node is at most
  the ambient length of the cut;
* every projected cut-child point is a proper ambient extension
  of the cut and hence is strictly longer than every retained
  old interior node;
* its new Q intrinsic rank is also strictly larger than that
  of every retained old interior node.

Consequently all old/new pairs with the new member arising from
a literal cut-child satisfy skew clause (iii) without any
assumption on the local D₂ bullet tail. The exceptional-terminal
marker family is still open, as are all remaining new/new
rank-sensitive comparisons.
-/

namespace DualTree.ForwardQOldCutChildOrder

open ForwardSourceQTree

/-- Every old interior source node precedes the final
source-interior cut in intrinsic source rank. -/
theorem old_interior_source_rank_le_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    SkewTree.heightAt c.source.tree s ≤
      SkewTree.heightAt c.source.tree c.cut := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have haux : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  exact ForwardFrontierRanks.rank_le_of_forwardAux
    c.source.tree hsemi.1 (ForwardQRooted.source_nonsingleton c)
    (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
    haux

/-- Every retained source interior node has ambient length
at most the cut length (the cut is forward-auxiliary maximal). -/
theorem old_interior_length_le_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    s.length ≤ c.cut.length := by
  have haux : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  rcases haux with hlt | ⟨heq, _⟩ <;> omega

/-- A projected point above a literal immediate child of the cut
is strictly longer than every retained old interior node. -/
theorem old_length_lt_projected_cut_child
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨c.cut ++ [i],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout i⟩
    s.length <
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨c.cut ++ [i],
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i⟩
  change s.length <
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length
  have hsource := old_interior_length_le_cut c s hs
  have hprefix : IsPrefix (c.cut ++ [i])
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
    exact ForwardQMarkerCoverage.marker_prefix_projected_point
      c x marker
  have hlength := prefix_length_le hprefix
  simp only [List.length_append, List.length_singleton] at hlength
  omega

/-- The Q rank of every cut-child projected point is strictly
above that of each retained original interior vertex. -/
theorem old_Q_rank_lt_projected_cut_child
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨c.cut ++ [i],
        ForwardStarredSignature.cut_child_mem_literalR
          c.source c.cut c.hout i⟩
    SkewTree.heightAt (nodes c x).toList s <
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨c.cut ++ [i],
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i⟩
  change SkewTree.heightAt (nodes c x).toList s <
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1
  have hrank : SkewTree.heightAt c.source.tree s ≤
      SkewTree.heightAt c.source.tree c.cut :=
    old_interior_source_rank_le_cut c s hs
  have hold := ForwardQRetainedRanks.original_interior_Q_height_eq_source
    c x s hs
  have hnew := ForwardQCutChildRank.projected_cut_child_Q_height
    c x i
  change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
    SkewTree.heightAt c.source.tree c.cut + 1 at hnew
  omega


/-- Every retained original interior vertex has Q intrinsic rank
at most that of every actual marked projected leaf.  In particular, the
new-to-old orientation of skew clause (iii) never occurs. This is
the combination of the exact old interior rank preservation and the
two-level band theorem for all D₂ projections. -/
theorem old_Q_rank_le_every_marked
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c)) :
    SkewTree.heightAt (nodes c x).toList s ≤
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 := by
  have hrank : SkewTree.heightAt c.source.tree s ≤
      SkewTree.heightAt c.source.tree c.cut :=
    old_interior_source_rank_le_cut c s hs
  have hold :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  rcases ForwardQMarkerRankBand.markedProjection_Q_rank_band
      hb c x i with hnew | hnew
  · omega
  · omega

end DualTree.ForwardQOldCutChildOrder
