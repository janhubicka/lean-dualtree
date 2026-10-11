import DualTree.ForwardSourceQTree
import DualTree.ForwardQAmbientRankClosure
import DualTree.VectorOneMarkedLengths

/-!
# Ambient T-rank order of genuine sorted D₂ projections

The actual corrected Q uses a finite subset D₂ of the forward-sorted
frontier coordinates of its ambient complete skew support T. For two
selected bullet coordinates i<j, the required starred-domain condition
provides nondecreasing lengths of their singleton local marked points.

We isolate that exact pairwise consequence as BulletLengthsOrdered,
rather than incorrectly claim that arbitrary elements of the ambient
mixed product have it. Linking the full Definition 20 W_* predicate to
this condition is an independent source-domain formalization task.

For ordered bullet coordinates the actual T-projection is monotone in
ambient support rank; if the local marked tail length strictly increases,
the T-rank strictly increases. Equality of projected T-ranks forces
equality of both frontier T-ranks and marked-point tail lengths.

These results are necessary tools for the new/new Q rank-transport
argument. They do not by themselves compare Q-intrinsic marker ranks
with the ordered D₂ indices, nor establish the full Q skew clauses.
-/

namespace DualTree.ForwardQIndexedTRanks

open ForwardSourceQTree

/-- Precisely the marked-point length monotonicity needed from the
starred vector-one-complete D₂ domain. It is *not* assumed of every
mixed-product input. -/
def BulletLengthsOrdered
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c) : Prop :=
  ∀ (i j : MixedProduct.BulletIndex (kind c)),
    i.1 < j.1 →
      (x.bulletPoint i).1.length ≤ (x.bulletPoint j).1.length

/-- The selected point actually advances the intrinsic T rank by
exactly its local marked tail length. -/
theorem marked_T_rank_formula
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    SkewTree.heightAt c.T (markedProjection c x i).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 +
        (x.bulletPoint i).1.length := by
  exact ForwardUniformConeDomains.projectCommon_height
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
    (x.bulletPoint i)

/-- The sorted D₂ points are forward-auxiliary ordered whenever
the source-domain marked singleton lengths are nondecreasing. -/
theorem marked_forwardAux_of_bullet_order
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    ForwardAux
      (markedProjection c x i).1
      (markedProjection c x j).1 := by
  exact ForwardSourceQTree.markedProjection_forward_order
    c x i j hij (hordered i j hij)

/-- The enclosing complete T-rank of the marked projections is
nondecreasing in actual sorted D₂ coordinate order. -/
theorem marked_T_rank_mono_of_bullet_order
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    SkewTree.heightAt c.T (markedProjection c x i).1 ≤
      SkewTree.heightAt c.T (markedProjection c x j).1 := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  exact ForwardFrontierRanks.rank_le_of_forwardAux
    c.T hc.1 c.hnon
    (markedProjection c x i).2 (markedProjection c x j).2
    (marked_forwardAux_of_bullet_order c x hordered i j hij)

/-- The ambient word lengths of the actual Q marked projections
are likewise nondecreasing in sorted D₂ coordinate order. -/
theorem marked_length_mono_of_bullet_order
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    (markedProjection c x i).1.length ≤
      (markedProjection c x j).1.length := by
  exact ForwardSourceQTree.markedProjection_length_le
    c x i j hij (hordered i j hij)

/-- Strictly increasing local bullet-point length forces strictly
increasing ambient T rank at sorted marked coordinates. The two
frontier ranks cannot decrease because they are sorted in forward
auxiliary order, and the actual projection formula is additive. -/
theorem marked_T_rank_lt_of_strict_point_length
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1)
    (htails : (x.bulletPoint i).1.length <
      (x.bulletPoint j).1.length) :
    SkewTree.heightAt c.T (markedProjection c x i).1 <
      SkewTree.heightAt c.T (markedProjection c x j).1 := by
  let f := ForwardOrderedProjections.frontierAt c.T c.cut i.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut j.1
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hfrontOrder : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut i.1 j.1 hij
  have hfrontRank :
      SkewTree.heightAt c.T f.1 ≤ SkewTree.heightAt c.T g.1 :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.T hc.1 c.hnon f.2 g.2 hfrontOrder
  have hri := marked_T_rank_formula c x i
  have hrj := marked_T_rank_formula c x j
  change SkewTree.heightAt c.T (markedProjection c x i).1 =
    SkewTree.heightAt c.T f.1 + (x.bulletPoint i).1.length at hri
  change SkewTree.heightAt c.T (markedProjection c x j).1 =
    SkewTree.heightAt c.T g.1 + (x.bulletPoint j).1.length at hrj
  omega

/-- Equality of the actual projected T-ranks at increasing
coordinates forces equality of both the frontier T-ranks and
their local marked-point lengths; neither summand can decrease. -/
theorem equal_T_rank_forces_equal_frontier_and_tail
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1)
    (heq : SkewTree.heightAt c.T (markedProjection c x i).1 =
      SkewTree.heightAt c.T (markedProjection c x j).1) :
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 ∧
    (x.bulletPoint i).1.length = (x.bulletPoint j).1.length := by
  let f := ForwardOrderedProjections.frontierAt c.T c.cut i.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut j.1
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hfrontOrder : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut i.1 j.1 hij
  have hfrontRank :
      SkewTree.heightAt c.T f.1 ≤ SkewTree.heightAt c.T g.1 :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.T hc.1 c.hnon f.2 g.2 hfrontOrder
  have hri := marked_T_rank_formula c x i
  have hrj := marked_T_rank_formula c x j
  have htailLe := hordered i j hij
  change SkewTree.heightAt c.T (markedProjection c x i).1 =
    SkewTree.heightAt c.T f.1 + (x.bulletPoint i).1.length at hri
  change SkewTree.heightAt c.T (markedProjection c x j).1 =
    SkewTree.heightAt c.T g.1 + (x.bulletPoint j).1.length at hrj
  -- Normalize the local frontier aliases in the conclusion as well:
  -- omega treats different syntactic spellings of the same term separately.
  change (SkewTree.heightAt c.T f.1 =
    SkewTree.heightAt c.T g.1) ∧
    (x.bulletPoint i).1.length = (x.bulletPoint j).1.length
  constructor <;> omega

end DualTree.ForwardQIndexedTRanks
