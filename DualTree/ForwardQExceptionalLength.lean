import DualTree.ForwardSourceRankAncestors
import DualTree.ForwardQExceptionalRanks
import DualTree.ForwardQRetainedOrder
import DualTree.ForwardProjectedTerminalOrder

/-!
# Strict ambient length of rank-(cut+1) exceptional Q replacements

The exceptional old-source terminal t has source rank either
h_S(cut) or h_S(cut)+1. The first case has the same Q intrinsic
rank as the cut and is controlled by the equal-rank lexical
argument; the second case must produce a strictly longer
ambient Q node.

The key is to choose a genuine source-support predecessor u
of t at rank h_S(cut). This is possible by the general
rank-by-rank rooted support path theorem. The ancestor u cannot
be below cut (the exceptional t is not), and cannot prefix cut
because both u and cut have equal source rank. Thus they lie
in incomparable prefix cones. Source skew clause (ii) and
maximality of cut in the corrected forward order imply
u <=lex cut.

If the first outside-inclusive-cut boundary r of t had length
at most the ambient length of cut, it would have the same
length as cut. Since u is an earlier source interior and
prefixes both r and t, the incomparable cone order forces
r <=lex cut. That would put r inside the inclusive cut,
contrary to its defining boundary property.

Therefore |cut| < |r| <= |P(r)| for every allowed local D2
tail. Together with Q's exact rank formulas, this settles
strict old/new skew clause (iii) for exceptional replacements
at rank h_S(cut)+1, independently of word/colouring issues.
-/

namespace DualTree.ForwardQExceptionalLength

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- An exceptional source leaf one source rank above the final
cut has its first outside-cut boundary strictly *longer* than
the cut's ambient word. The ancestor at cut rank is obtained
from actual finite source geometry, not assumed. -/
theorem exceptional_boundary_strict_length
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank :
      SkewTree.heightAt c.source.tree t.1 =
        SkewTree.heightAt c.source.tree c.cut + 1) :
    c.cut.length <
      (firstBoundary c.cut t.1 (c.hout t.1 t.2)).length := by
  let r := firstBoundary c.cut t.1 (c.hout t.1 t.2)
  have htSpec :=
    StarredSignature.exceptionalLeaves_spec c.source c.cut t.1 t.2
  have hsource : t.1 ∈ c.source.tree := htSpec.1
  have hnotCutT : ¬ IsPrefix c.cut t.1 := htSpec.2.2
  have hgreater :
      SkewTree.heightAt c.source.tree c.cut <
        SkewTree.heightAt c.source.tree t.1 := by omega
  obtain ⟨u, huSource, huStrict, huRank⟩ :=
    ForwardSourceRankAncestors.source_strict_ancestor_at_cut_rank
      c t.1 hsource hgreater
  have huInterior : u ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree u t.1 huSource hsource huStrict
  have huForward : ForwardAux u c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax u huInterior
  have huNeCut : u ≠ c.cut := by
    intro heq
    subst u
    exact hnotCutT huStrict.1
  have huNotPrefixCut : ¬ IsPrefix u c.cut := by
    intro hup
    have hrankLt :=
      SupportHeightRanks.heightAt_lt_of_strictPrefix
        c.source.tree huSource ⟨hup, huNeCut⟩
    omega
  have hcutNotPrefixU : ¬ IsPrefix c.cut u := by
    intro hcu
    exact hnotCutT (isPrefix_trans hcu huStrict.1)
  have huLexCut : FinLexLE u c.cut :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.source.tree (ForwardQRetainedOrder.source_condIIB c)
      u c.cut huSource (List.mem_filter.mp c.hcut).1
      huRank huForward
  have hrSpec : Boundary c.cut t.1 r :=
    firstBoundary_spec c.cut t.1 (c.hout t.1 t.2)
  have hrOutside :
      ¬ ForwardAux r c.cut :=
    (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      c.source c.cut c.hout t.1 t.2).1
  have hcutLenLe : c.cut.length ≤ r.length := by
    by_contra hn
    exact hrOutside (Or.inl (by omega))
  have huLenLe : u.length ≤ c.cut.length := by
    rcases huForward with hlt | ⟨heq, _⟩ <;> omega
  change c.cut.length < r.length
  by_contra hn
  have hlenEq : r.length = c.cut.length := by omega
  have huLenR : u.length ≤ r.length := by omega
  have huPrefixR : IsPrefix u r :=
    CutFrontier.prefix_of_prefix_length_le
      huStrict.1 hrSpec.1 huLenR
  rcases huPrefixR with ⟨tail, hrtail⟩
  have hlexExtensions : FinLexLE (u ++ tail) (c.cut ++ []) :=
    ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      u c.cut tail [] huLexCut huNotPrefixCut hcutNotPrefixU
  have hlexRCut : FinLexLE r c.cut := by
    rw [← hrtail] at hlexExtensions
    simpa using hlexExtensions
  exact hrOutside (Or.inr ⟨hlenEq, hlexRCut⟩)

/-- Every genuine Q projection replacing an exceptional
source terminal at the cut's next intrinsic rank is strictly
longer than the source cut, regardless of its local bullet
point and cone-tail length. -/
theorem exceptional_projection_strict_length
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank :
      SkewTree.heightAt c.source.tree t.1 =
        SkewTree.heightAt c.source.tree c.cut + 1) :
    let marker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    c.cut.length <
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        c.source c.cut c.hmax c.hout t⟩
  change c.cut.length <
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length
  have hrlen := exceptional_boundary_strict_length c t htRank
  have hrproj : IsPrefix marker.1
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 :=
    ForwardQMarkerCoverage.marker_prefix_projected_point c x marker
  have hrprojLen := prefix_length_le hrproj
  change c.cut.length < marker.1.length at hrlen
  omega

/-- For a source exceptional terminal at rank cut+1,
every retained old Q interior node has both smaller
intrinsic Q rank and shorter ambient length than its
actual Q replacement. This is the remaining exceptional
family of mixed old/new skew clause (iii). -/
theorem old_strict_below_exceptional_projection
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank :
      SkewTree.heightAt c.source.tree t.1 =
        SkewTree.heightAt c.source.tree c.cut + 1) :
    let marker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    SkewTree.heightAt (nodes c x).toList s <
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c marker)).1 ∧
    s.length <
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        c.source c.cut c.hmax c.hout t⟩
  change
    SkewTree.heightAt (nodes c x).toList s <
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c marker)).1 ∧
    s.length <
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length
  have hsBefore : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hsLen : s.length ≤ c.cut.length := by
    rcases hsBefore with hlt | ⟨heq, _⟩ <;> omega
  have hsourceSkew := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsourceSkew
  have hsRank :
      SkewTree.heightAt c.source.tree s ≤
        SkewTree.heightAt c.source.tree c.cut :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.source.tree hsourceSkew.1
      (ForwardQRooted.source_nonsingleton c)
      (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
      hsBefore
  have hQranksOld :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  have hQranksNew :=
    ForwardQExceptionalRanks.exceptional_projection_Q_rank_eq_source
      c x t
  change SkewTree.heightAt (nodes c x).toList
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
    SkewTree.heightAt c.source.tree t.1 at hQranksNew
  have hlength :=
    exceptional_projection_strict_length c x t htRank
  change c.cut.length <
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1.length at hlength
  constructor <;> omega

end DualTree.ForwardQExceptionalLength
