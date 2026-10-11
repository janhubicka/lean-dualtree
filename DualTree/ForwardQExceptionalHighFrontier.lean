import DualTree.ForwardQExceptionalLength
import DualTree.ForwardQMarkerCoverage
import DualTree.ForwardQRetainedOrder
import DualTree.ForwardProjectedTerminalOrder
import DualTree.ForwardSourceRankAncestors

/-!
# The selected ambient frontier of an exceptional terminal stays on its path

An exceptional source terminal t contributes the first boundary r
outside the repaired forward cut. Its unique selected minimal
ambient complete-support frontier f extends r. While this alone
does not formally say that f is on the path to t, it follows from
meet-closure: f and t both extend r, and their ambient meet is
a T-support node still outside the cut. Minimality of f makes
that meet f itself.

For an exceptional terminal of source rank h_S(cut)+1, the
rank-by-rank predecessor theorem supplies a source interior
ancestor u of rank h_S(cut). This ancestor is in a different
prefix cone from cut, lexicographically to its left; the
selected frontier f extends u and is in the same left cone.
If f had T-rank h_T(cut), the enclosing T skew clause (ii)
would put f before the cut in the corrected forward order.
That contradicts its outside-cut frontier property. Thus
h_T(f)=h_T(cut)+1 by the checked two-level frontier bound.

This settles the ambient T-frontier rank of the *high-rank*
exceptional family. The low-rank family is separate; the Q
word and colouring remain open.
-/

namespace DualTree.ForwardQExceptionalHighFrontier

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- The actual selected minimal outside-cut T frontier of an
exceptional source terminal lies on that terminal's ambient
root-to-leaf path, not merely somewhere in the same boundary cone. -/
theorem exceptional_frontier_prefix_terminal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut}) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1).1
      t.1 := by
  let r := firstBoundary c.cut t.1 (c.hout t.1 t.2)
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨r, ForwardQInteriorExact.exceptional_boundary_mem_literalR
      c.source c.cut c.hmax c.hout t⟩
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut
    (ForwardQMarkerCoverage.bulletForMarker c marker).1).1
  change IsPrefix f t.1
  have hfFront : CutFrontier.Frontier c.T
      (fun v => ForwardAux v c.cut) f :=
    ForwardOrderedProjections.frontierAt_spec
      c.T c.cut (ForwardQMarkerCoverage.bulletForMarker c marker).1
  have hrF : IsPrefix r f := by
    have h :=
      (ForwardLiteralFrontierCoordinates.frontierFor_spec
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly marker).2
    rw [← ForwardQMarkerCoverage.bullet_frontier_eq_marker_frontier
      c marker] at h
    exact h
  have hrT : IsPrefix r t.1 :=
    (firstBoundary_spec c.cut t.1 (c.hout t.1 t.2)).1
  let meet := MeetGeometry.commonPrefix f t.1
  have hMeetT : meet ∈ c.T :=
    (ForwardInclusiveFrontier.meetClosed_complete_forward
      c.T c.hcomplete c.hnon)
      f t.1 hfFront.1
      (c.hST t.1
        (StarredSignature.exceptionalLeaves_spec
          c.source c.cut t.1 t.2).1)
  have hrMeet : IsPrefix r meet :=
    MeetGeometry.prefix_commonPrefix hrF hrT
  have hrOutside : ¬ ForwardAux r c.cut :=
    (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      c.source c.cut c.hout t.1 t.2).1
  have hMeetOutside : ¬ ForwardAux meet c.cut :=
    ForwardInclusiveFrontier.outside_of_prefix
      hrOutside hrMeet
  have hMeetF : IsPrefix meet f :=
    MeetGeometry.commonPrefix_prefix_left f t.1
  have hMeetEq : meet = f := by
    by_contra hne
    exact hMeetOutside
      (hfFront.2.2 meet hMeetT ⟨hMeetF, hne⟩)
  have hMeetTpre : IsPrefix meet t.1 :=
    MeetGeometry.commonPrefix_prefix_right f t.1
  rw [hMeetEq] at hMeetTpre
  exact hMeetTpre

/-- A source exceptional terminal one intrinsic source level
above cut has selected minimal ambient T-frontier exactly
one intrinsic T-level above cut. -/
theorem exceptional_high_frontier_T_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank : SkewTree.heightAt c.source.tree t.1 =
      SkewTree.heightAt c.source.tree c.cut + 1) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1).1 =
      SkewTree.heightAt c.T c.cut + 1 := by
  let r := firstBoundary c.cut t.1 (c.hout t.1 t.2)
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨r, ForwardQInteriorExact.exceptional_boundary_mem_literalR
      c.source c.cut c.hmax c.hout t⟩
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut
    (ForwardQMarkerCoverage.bulletForMarker c marker).1).1
  change SkewTree.heightAt c.T f =
    SkewTree.heightAt c.T c.cut + 1
  have htSource : t.1 ∈ c.source.tree :=
    (StarredSignature.exceptionalLeaves_spec
      c.source c.cut t.1 t.2).1
  have hnotCutT : ¬ IsPrefix c.cut t.1 :=
    (StarredSignature.exceptionalLeaves_spec
      c.source c.cut t.1 t.2).2.2
  have hgreater : SkewTree.heightAt c.source.tree c.cut <
      SkewTree.heightAt c.source.tree t.1 := by omega
  obtain ⟨u, huSource, huStrictT, huRank⟩ :=
    ForwardSourceRankAncestors.source_strict_ancestor_at_cut_rank
      c t.1 htSource hgreater
  have huInterior : u ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree u t.1 huSource htSource huStrictT
  have huEarly : ForwardAux u c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax u huInterior
  have huNotCut : u ≠ c.cut := by
    intro heq
    subst u
    exact hnotCutT huStrictT.1
  have huNotPreCut : ¬ IsPrefix u c.cut := by
    intro hpre
    have hlt :=
      SupportHeightRanks.heightAt_lt_of_strictPrefix
        c.source.tree huSource ⟨hpre, huNotCut⟩
    omega
  have hcutNotPreU : ¬ IsPrefix c.cut u := by
    intro hpre
    exact hnotCutT (isPrefix_trans hpre huStrictT.1)
  have huLexCut : FinLexLE u c.cut :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.source.tree (ForwardQRetainedOrder.source_condIIB c)
      u c.cut huSource (List.mem_filter.mp c.hcut).1
      huRank huEarly
  have hfFront : CutFrontier.Frontier c.T
      (fun v => ForwardAux v c.cut) f :=
    ForwardOrderedProjections.frontierAt_spec
      c.T c.cut (ForwardQMarkerCoverage.bulletForMarker c marker).1
  have hfPreT : IsPrefix f t.1 := by
    exact exceptional_frontier_prefix_terminal c t
  have hrF : IsPrefix r f := by
    have h :=
      (ForwardLiteralFrontierCoordinates.frontierFor_spec
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly marker).2
    rw [← ForwardQMarkerCoverage.bullet_frontier_eq_marker_frontier
      c marker] at h
    exact h
  have hrLen : c.cut.length < r.length :=
    ForwardQExceptionalLength.exceptional_boundary_strict_length
      c t htRank
  have huLen : u.length ≤ c.cut.length := by
    rcases huEarly with hlt | ⟨heq, _⟩ <;> omega
  have hrFLen : r.length ≤ f.length := prefix_length_le hrF
  have huPreF : IsPrefix u f :=
    CutFrontier.prefix_of_prefix_length_le
      huStrictT.1 hfPreT (by omega)
  have hfLexCut : FinLexLE f c.cut := by
    rcases huPreF with ⟨tail, htail⟩
    have hlex :=
      ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
        u c.cut tail [] huLexCut huNotPreCut hcutNotPreU
    simpa [htail] using hlex
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hband :=
    ForwardFrontierRanks.frontier_rank_band
      c.T hc.1 c.hnon c.cut f c.hcutT hfFront
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hcore := hskew.2
  simp [c.hnon, Bool.and_eq_true] at hcore
  have hII : SkewTree.condIIB c.T = true := hcore.1.1.2
  rcases hband with hsame | hnext
  · have hwrong : ForwardAux f c.cut :=
      ForwardOrderCompatibility.forwardAux_of_equal_height_lex
        c.T hII f c.cut hfFront.1 c.hcutT hsame
        hfLexCut
    exact False.elim (hfFront.2.1 hwrong)
  · exact hnext

end DualTree.ForwardQExceptionalHighFrontier
