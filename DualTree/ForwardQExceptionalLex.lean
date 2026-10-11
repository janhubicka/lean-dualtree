import DualTree.ForwardQOldCutChildOrder
import DualTree.ForwardQExceptionalRanks
import DualTree.ForwardProjectedTerminalOrder
import DualTree.ForwardAuxTransitivity

/-!
# Lexicographic position of equal-rank exceptional Q replacements

The corrected Q reconstruction replaces a source exceptional leaf t
by a projected point above its first forward-cut exit marker r.  The
source has the forward-skew same-rank length condition; when t has
the same intrinsic source rank as the final cut, the old cut must
precede t in *ordinary* lexicographic order.

The first exit r and cut lie in incomparable cones, and r is a
prefix of t.  A generic finite-word lemma transports that strict
lexicographic cone comparison backwards to r and then forwards
to every Q projection above r.

This proves that when a source exceptional leaf has the cut rank,
its Q replacement is lexicographically to the right of the cut,
and hence of every retained source interior vertex of the cut
rank.  This is the missing lexicographic orientation needed to
handle same-rank mixed Q pairs under skew clause (ii).

It does not prove the strict ambient-length comparison for
exceptional replacements at the cut rank plus one, nor the
remaining new/new comparisons or the Q word and colouring.
-/

namespace DualTree.ForwardQExceptionalLex

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- If g is a prefix of u and f and g are incomparable in the
ambient prefix tree, then a forward lex comparison f ≤ u
already forces f ≤ g. This is a generic finite-word fact;
it uses ordinary lex antisymmetry and cone-extension order. -/
theorem lex_of_lex_extension_of_incomparable {b : Nat}
    (f g u : Node b)
    (hgu : IsPrefix g u)
    (hfg : ¬ IsPrefix f g)
    (hgf : ¬ IsPrefix g f)
    (hfu : FinLexLE f u) :
    FinLexLE f g := by
  rcases hgu with ⟨tail, rfl⟩
  rcases finLexLE_total f g with hfgLex | hgfLex
  · exact hfgLex
  · have huf : FinLexLE (g ++ tail) f := by
      simpa using
        (ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
          g f tail [] hgfLex hgf hfg)
    have heq : f = g ++ tail :=
      PaperAuxAntisymm.finLexLE_antisymm
        f (g ++ tail) hfu huf
    have hgfPre : IsPrefix g f := ⟨tail, heq⟩
    exact False.elim (hgf hgfPre)

/-- When an exceptional source leaf is at the same intrinsic
rank as the maximal cut, its *actual* Q replacement lies to
the right of the cut in ordinary forward lex order. -/
theorem cut_lex_exceptional_equal_rank_projection
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (hrank : SkewTree.heightAt c.source.tree t.1 =
      SkewTree.heightAt c.source.tree c.cut) :
    let marker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    FinLexLE c.cut
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
  let r := firstBoundary c.cut t.1 (c.hout t.1 t.2)
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨r, ForwardQInteriorExact.exceptional_boundary_mem_literalR
      c.source c.cut c.hmax c.hout t⟩
  change FinLexLE c.cut
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1
  have hterminal := StarredSignature.exceptionalLeaves_spec
    c.source c.cut t.1 t.2
  have hfrontier :=
    ForwardQExceptionalRanks.exceptional_is_source_frontier hb c t.1 t.2
  have hcutT : ForwardAux c.cut t.1 := by
    rcases CanonicalForwardAuxIso.forwardAux_total c.cut t.1 with
      hforward | hreverse
    · exact hforward
    · exact False.elim (hfrontier.2.1 hreverse)
  have hcutLexT : FinLexLE c.cut t.1 :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.source.tree (ForwardQRetainedOrder.source_condIIB c)
      c.cut t.1 (List.mem_filter.mp c.hcut).1
      hterminal.1 hrank.symm hcutT
  have hrSpec : Boundary c.cut t.1 r :=
    firstBoundary_spec c.cut t.1 (c.hout t.1 t.2)
  have hrBound : ForwardInclusiveFrontier.ForwardCutBoundary c.cut r :=
    ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      c.source c.cut c.hout t.1 t.2
  have hcutNotR : ¬ IsPrefix c.cut r := by
    intro hpre
    exact hterminal.2.2 (isPrefix_trans hpre hrSpec.1)
  have hrNotCut : ¬ IsPrefix r c.cut := by
    intro hpre
    exact hrBound.1 (ForwardInclusiveFrontier.forwardAux_of_prefix
      hpre (CanonicalForwardAuxIso.forwardAux_refl c.cut))
  have hlexCutR : FinLexLE c.cut r :=
    lex_of_lex_extension_of_incomparable
      c.cut r t.1 hrSpec.1 hcutNotR hrNotCut hcutLexT
  have hrProjected : IsPrefix r
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
    exact ForwardQMarkerCoverage.marker_prefix_projected_point
      c x marker
  rcases hrProjected with ⟨tail, hproj⟩
  rw [hproj]
  simpa using
    (ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      c.cut r [] tail hlexCutR hcutNotR hrNotCut)

/-- Every retained interior vertex at the maximal cut's source
rank precedes an equal-source-rank exceptional Q replacement
in the ordinary forward lex order. -/
theorem old_top_rank_lex_exceptional_equal_rank_projection
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (hsRank : SkewTree.heightAt c.source.tree s =
      SkewTree.heightAt c.source.tree c.cut)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank : SkewTree.heightAt c.source.tree t.1 =
      SkewTree.heightAt c.source.tree c.cut) :
    let marker : ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    FinLexLE s
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        c.source c.cut c.hmax c.hout t⟩
  change FinLexLE s
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1
  have hsEarly : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hlexSCut : FinLexLE s c.cut :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.source.tree (ForwardQRetainedOrder.source_condIIB c)
      s c.cut (List.mem_filter.mp hs).1
      (List.mem_filter.mp c.hcut).1 hsRank hsEarly
  have hlexCutProjected :=
    cut_lex_exceptional_equal_rank_projection hb c x t htRank
  change FinLexLE c.cut
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c marker)).1 at hlexCutProjected
  exact ForwardAuxTransitivity.finLexLE_trans
    s c.cut _ hlexSCut hlexCutProjected

end DualTree.ForwardQExceptionalLex
