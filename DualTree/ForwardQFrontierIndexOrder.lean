import DualTree.ForwardSourceQTree
import DualTree.ForwardProjectedTerminalOrder
import DualTree.ForwardFrontierRanks

/-!
# Order of sorted D₂ indices from their ambient frontier geometry

The actual sorted minimal T-frontier coordinates are indexed by Fin d,
and the selected bullet indices are subtypes of those Fin d positions.
Sorting in forward auxiliary order makes the intrinsic T rank of the
frontiers nondecreasing in the coordinate index.

More subtly, if two selected frontier roots have equal T rank,
their projected Q leaves inherit exactly the lexicographic order of
those roots: the distinct frontier cones are prefix-incomparable.
The ambient skew same-rank condition says that in this case the
forward auxiliary order of the roots agrees with lexicographic order.

Consequently if the *projections* are lexicographically ordered
and their frontier roots have equal ambient T rank, the selected
bullet indices occur in the same order. This does not require any
assumption about local D₂ tail lengths.

These two lemmas are independent of the source marker rank bands.
They can later be combined with those bands and the starred
marked-point length monotonicity to close the new/new Q skew
conditions.
-/

namespace DualTree.ForwardQFrontierIndexOrder

open ForwardSourceQTree

/-- Selected minimal T-frontier intrinsic ranks are
nondecreasing in their genuine sorted D₂ coordinate order. -/
theorem frontier_T_rank_mono
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 ≤
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 := by
  let f := ForwardOrderedProjections.frontierAt c.T c.cut i.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut j.1
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hfg : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut i.1 j.1 hij
  exact ForwardFrontierRanks.rank_le_of_forwardAux
    c.T hc.1 c.hnon f.2 g.2 hfg

/-- For two different selected D₂ projections whose frontier
roots have the same intrinsic T rank, forward lex order of
the projections forces increasing sorted bullet index.
The incomparability of the distinct frontier cones makes
this independent of their local tails. -/
theorem bullet_index_le_of_equal_frontier_rank_lex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hfrontRank :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1)
    (hlex : FinLexLE (markedProjection c x i).1
      (markedProjection c x j).1) :
    i.1 ≤ j.1 := by
  by_contra hn
  have hji : j.1 < i.1 := by omega
  let f := ForwardOrderedProjections.frontierAt c.T c.cut j.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut i.1
  have hfg : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut j.1 i.1 hji
  have hrank : SkewTree.heightAt c.T f.1 =
      SkewTree.heightAt c.T g.1 := hfrontRank.symm
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hcore := hskew.2
  simp [c.hnon, Bool.and_eq_true] at hcore
  have hII : SkewTree.condIIB c.T = true := hcore.1.1.2
  have hlexFG : FinLexLE f.1 g.1 :=
    ForwardProjectedTerminalOrder.lex_of_equal_rank_forwardAux
      c.T hII f.1 g.1 f.2 g.2 hrank hfg
  have hfNeG : f.1 ≠ g.1 := by
    intro heq
    have heqIndex : j.1 = i.1 :=
      ForwardOrderedProjections.frontierAt_injective
        c.T c.cut (Subtype.ext heq)
    exact (ne_of_lt hji) heqIndex
  have hnotPrefixes :=
    ForwardProjectedTerminalOrder.frontiers_incomparable
      c.T c.cut f.1 g.1
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
      hfNeG
  have hpreJ : IsPrefix f.1 (markedProjection c x j).1 :=
    ForwardSourceQTree.markedProjection_cone c x j
  have hpreI : IsPrefix g.1 (markedProjection c x i).1 :=
    ForwardSourceQTree.markedProjection_cone c x i
  have hlexJI : FinLexLE (markedProjection c x j).1
      (markedProjection c x i).1 := by
    rcases hpreJ with ⟨tailJ, heqJ⟩
    rcases hpreI with ⟨tailI, heqI⟩
    rw [heqJ, heqI]
    exact ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      f.1 g.1 tailJ tailI
      hlexFG hnotPrefixes.1 hnotPrefixes.2
  have heqNodes : (markedProjection c x i).1 =
      (markedProjection c x j).1 :=
    PaperAuxAntisymm.finLexLE_antisymm
      (markedProjection c x i).1
      (markedProjection c x j).1 hlex hlexJI
  have heqBullets : i = j :=
    ForwardSourceQTree.markedProjection_injective
      c x (Subtype.ext heqNodes)
  exact (ne_of_lt hji) (congrArg Subtype.val heqBullets).symm

end DualTree.ForwardQFrontierIndexOrder
