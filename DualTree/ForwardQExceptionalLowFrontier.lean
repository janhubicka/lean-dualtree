import DualTree.ForwardQExceptionalHighFrontier
import DualTree.ForwardQExceptionalLex
import DualTree.ForwardCompleteEmbedding
import DualTree.ForwardSourceRankAncestors

/-!
# Low-rank exceptional terminals have lower ambient T-frontier rank

The corrected source S and ambient complete skew support T have
different intrinsic rank functions. Their cuts have respective
ranks m=h_S(cut) and M=h_T(cut).

For an exceptional source terminal t of source rank m, compare it
with cut in the original source's skew clause (ii): the terminal
is after cut in forward auxiliary order, hence cut ≤lex t.

Because T is complete and t∈T, its support path contains a
T-vertex a of intrinsic T rank M. The original terminal t
does not descend from cut. Therefore a and cut are prefix-
incomparable, and the lex order cut ≤lex t reflects back to
cut ≤lex a. T skew clause (ii) puts a outside the inclusive
forward cut.

The genuine minimal T-frontier f selected for t lies on the
path to t (proved in ForwardQExceptionalHighFrontier). It
must be at or before a on this path: otherwise a would be
an earlier outside-cut T node, violating minimality of f.
Consequently h_T(f) ≤ h_T(a)=M. The general outside-cut
frontier rank lower bound gives the reverse inequality.

Thus h_T(f)=h_T(cut) for the low-rank exceptional family.
Together with the high-rank exceptional and literal cut-child
frontier theorems, this gives the two-band frontier matching
needed for new/new Q skewness, without yet asserting any
vector-word or colouring compatibility.
-/

namespace DualTree.ForwardQExceptionalLowFrontier

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- Every T-vertex of intrinsic T rank at least that of
the source cut has a genuine T-support ancestor at exactly
the cut T rank. Completeness provides the common support
root and Nodup; no ambient length monotonicity is assumed. -/
theorem ambient_ancestor_at_cut_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ c.T)
    (hle : SkewTree.heightAt c.T c.cut ≤
      SkewTree.heightAt c.T t) :
    ∃ a : Node b,
      a ∈ c.T ∧ IsPrefix a t ∧
      SkewTree.heightAt c.T a =
        SkewTree.heightAt c.T c.cut := by
  exact ForwardSourceRankAncestors.ancestor_at_each_rank
    c.T (ForwardCompleteEmbedding.support_nodup c.T c.hcomplete)
    (ForwardCompleteEmbedding.rootOf c.T c.hcomplete c.hnon)
    (ForwardCompleteEmbedding.rootOf_mem c.T c.hcomplete c.hnon)
    (fun v hv =>
      ForwardCompleteEmbedding.rootOf_prefix
        c.T c.hcomplete c.hnon v hv)
    t ht (SkewTree.heightAt c.T c.cut) hle

/-- When an actual exceptional source leaf has the source
cut's intrinsic rank, its actual selected T frontier has
the *ambient T cut rank* (not merely one of two levels). -/
theorem exceptional_low_frontier_T_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (htRank : SkewTree.heightAt c.source.tree t.1 =
      SkewTree.heightAt c.source.tree c.cut) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut
        (ForwardQMarkerCoverage.bulletForMarker c marker).1).1 =
      SkewTree.heightAt c.T c.cut := by
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        c.source c.cut c.hmax c.hout t⟩
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut
    (ForwardQMarkerCoverage.bulletForMarker c marker).1).1
  change SkewTree.heightAt c.T f =
    SkewTree.heightAt c.T c.cut
  have htSpec :=
    StarredSignature.exceptionalLeaves_spec
      c.source c.cut t.1 t.2
  have htSource : t.1 ∈ c.source.tree := htSpec.1
  have htT : t.1 ∈ c.T := c.hST t.1 htSource
  have hnotCutT : ¬ IsPrefix c.cut t.1 := htSpec.2.2
  have htNeCut : t.1 ≠ c.cut := by
    intro heq
    apply hnotCutT
    rw [heq]
    exact isPrefix_refl c.cut
  have htOutside : ¬ ForwardAux t.1 c.cut := by
    intro h
    exact c.hout t.1 t.2 ⟨h, htNeCut⟩
  have hcutBeforeT : ForwardAux c.cut t.1 := by
    rcases CanonicalForwardAuxIso.forwardAux_total
        c.cut t.1 with h | h
    · exact h
    · exact False.elim (htOutside h)
  have hcutLexT : FinLexLE c.cut t.1 :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.source.tree (ForwardQRetainedOrder.source_condIIB c)
      c.cut t.1 (List.mem_filter.mp c.hcut).1
      htSource htRank.symm hcutBeforeT
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hTrankLe :
      SkewTree.heightAt c.T c.cut ≤
        SkewTree.heightAt c.T t.1 :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.T hc.1 c.hnon c.hcutT htT hcutBeforeT
  obtain ⟨a, haT, haPreT, haRank⟩ :=
    ambient_ancestor_at_cut_rank c t.1 htT hTrankLe
  have haNeCut : a ≠ c.cut := by
    intro heq
    subst a
    exact hnotCutT haPreT
  have hcutNotPreA : ¬ IsPrefix c.cut a := by
    intro hpre
    exact hnotCutT (isPrefix_trans hpre haPreT)
  have haNotPreCut : ¬ IsPrefix a c.cut := by
    intro hpre
    have hEq :=
      SupportHeightRanks.heightAt_injective_on_common_path
        c.T haT c.hcutT hpre
        (isPrefix_refl c.cut) haRank
    exact haNeCut hEq
  have hcutLexA : FinLexLE c.cut a :=
    ForwardQExceptionalLex.lex_of_lex_extension_of_incomparable
      c.cut a t.1 haPreT hcutNotPreA haNotPreCut
      hcutLexT
  have hparts := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have hcore := hparts.2
  simp [c.hnon, Bool.and_eq_true] at hcore
  have hII : SkewTree.condIIB c.T = true := hcore.1.1.2
  have hCutBeforeA : ForwardAux c.cut a :=
    ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      c.T hII c.cut a c.hcutT haT haRank.symm hcutLexA
  have haOutside : ¬ ForwardAux a c.cut := by
    intro hac
    have hcutEqA :=
      CanonicalForwardAuxIso.forwardAux_antisymm
        hCutBeforeA hac
    exact haNeCut hcutEqA.symm
  have hfFront : CutFrontier.Frontier c.T
      (fun v => ForwardAux v c.cut) f :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut
      (ForwardQMarkerCoverage.bulletForMarker c marker).1
  have hfPreT : IsPrefix f t.1 :=
    ForwardQExceptionalHighFrontier.exceptional_frontier_prefix_terminal
      c t
  have hfPreA : IsPrefix f a := by
    rcases le_total f.length a.length with hlen | hlen
    · exact CutFrontier.prefix_of_prefix_length_le
        hfPreT haPreT hlen
    · have haPreF : IsPrefix a f :=
        CutFrontier.prefix_of_prefix_length_le
          haPreT hfPreT hlen
      by_cases heq : a = f
      · subst a
        exact isPrefix_refl f
      · have hstrict : IsStrictPrefix a f := ⟨haPreF, heq⟩
        have haBefore : ForwardAux a c.cut :=
          hfFront.2.2 a haT hstrict
        exact False.elim (haOutside haBefore)
  have hfBeforeA : ForwardAux f a :=
    ForwardInclusiveFrontier.forwardAux_of_prefix
      hfPreA (CanonicalForwardAuxIso.forwardAux_refl a)
  have hfRankLe :
      SkewTree.heightAt c.T f ≤ SkewTree.heightAt c.T a :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.T hc.1 c.hnon hfFront.1 haT hfBeforeA
  have hfRankGe :=
    ForwardFrontierRanks.cut_rank_le_frontier
      c.T hc.1 c.hnon c.cut f c.hcutT hfFront
  omega

end DualTree.ForwardQExceptionalLowFrontier
