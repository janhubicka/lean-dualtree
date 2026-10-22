import DualTree.ForwardQFinalTargetRankGap
import DualTree.ForwardFrontierRanks

/-!
# Lemma 27: target terminal ranks at the two frontier bands

The final selected target D₂ points already give an exact raw Q
preimage. Their corrected starred-domain condition is equivalent to
a compensated target-T-rank inequality. This module simplifies that
condition using the *actual* two-level frontier rank band.

Every minimal outside-cut T-frontier has rank m or m+1. The sorted
D₂ frontier ranks are nondecreasing. Consequently a target-selected
D₂ family is starred precisely if its terminal T-ranks are
nondecreasing and increase STRICTLY across a jump from frontier
rank m to m+1.

This is a reduction of the outstanding proof obligation, not a
claim that the target signature, local mixed span or printed
reverse-lex W_* automatically supplies the required inequalities.
In particular terminal ranks must NOT simply be compared as if
every frontier had the same rank.
-/

namespace DualTree.ForwardQFinalTargetRankBands

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetRankGap

/-- The enclosing complete-T height of the actual source D₂
frontier coordinate, independent of any chosen Q marker point. -/
noncomputable def frontierTRank
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (i : MixedProduct.BulletIndex (kind g.core)) : Nat :=
  SkewTree.heightAt g.core.T
    (ForwardOrderedProjections.frontierAt
      g.core.T g.core.cut i.1).1

/-- The enclosing complete-T height of the unique terminal
requested by O at the actual corrected selected D₂ coordinate. -/
noncomputable def terminalTRank
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (i : MixedProduct.BulletIndex (kind g.core)) : Nat :=
  SkewTree.heightAt g.core.T
    (targetTerminalAtBullet hb g f O L hSupport i)

/-- Actual corrected D₂ frontiers are T-rank sorted: this
uses the full complete-skew property, not just their lengths. -/
theorem frontierTRank_mono
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1) :
    frontierTRank g i ≤ frontierTRank g j := by
  have hc := g.core.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  exact ForwardFrontierRanks.ordered_frontiers_rank_le
    g.core.T hc.1 g.core.hnon g.core.cut
    (ForwardOrderedProjections.frontierAt
      g.core.T g.core.cut i.1).1
    (ForwardOrderedProjections.frontierAt
      g.core.T g.core.cut j.1).1
    (ForwardOrderedProjections.frontierAt_spec
      g.core.T g.core.cut i.1)
    (ForwardOrderedProjections.frontierAt_spec
      g.core.T g.core.cut j.1)
    (ForwardSortedFrontiers.frontiers_get_order
      g.core.T g.core.cut i.1 j.1 hij)

/-- Every selected D₂ frontier lies in one of precisely two
T-rank bands, m or m+1, where m is the T-rank of the cut. -/
theorem frontierTRank_band
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    frontierTRank g i = m ∨ frontierTRank g i = m + 1 := by
  have hc := g.core.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have h :=
    ForwardFrontierRanks.frontier_rank_band
      g.core.T hc.1 g.core.hnon g.core.cut
      (ForwardOrderedProjections.frontierAt
        g.core.T g.core.cut i.1).1
      g.core.hcutT
      (ForwardOrderedProjections.frontierAt_spec
        g.core.T g.core.cut i.1)
  simpa only [frontierTRank, g.core.hm] using h

/-- A target-only formulation of the remaining corrected D₂
admissibility condition, with no arithmetic compensation:
terminal ranks must be nondecreasing, and strictly increasing
whenever the source frontier rank jumps. -/
def TargetTerminalRankJumpOrder
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) : Prop :=
  ∀ i j : MixedProduct.BulletIndex (kind g.core), i.1 < j.1 →
    terminalTRank hb g f O L hSupport i ≤
      terminalTRank hb g f O L hSupport j ∧
    (frontierTRank g i < frontierTRank g j →
      terminalTRank hb g f O L hSupport i <
        terminalTRank hb g f O L hSupport j)

/-- The compensated T-rank criterion is EXACTLY the terminal
weak-order plus strict cross-frontier-band-order criterion.
The reverse implication depends essentially on the m/m+1 band,
not on an unsupported equal-frontier-rank assertion. -/
theorem target_rank_gaps_iff_terminal_rank_jump_order
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q)) :
    TargetRankGapsOrdered hb g f O L hSupport ↔
      TargetTerminalRankJumpOrder hb g f O L hSupport := by
  constructor
  · intro hgap i j hij
    have hfront : frontierTRank g i ≤ frontierTRank g j :=
      frontierTRank_mono g i j hij
    have hcompensated := hgap i j hij
    change terminalTRank hb g f O L hSupport i +
        frontierTRank g j ≤
      terminalTRank hb g f O L hSupport j +
        frontierTRank g i at hcompensated
    constructor
    · omega
    · intro hstrictFront
      omega
  · intro hjump i j hij
    have hfront : frontierTRank g i ≤ frontierTRank g j :=
      frontierTRank_mono g i j hij
    have hbandI := frontierTRank_band g i
    have hbandJ := frontierTRank_band g j
    obtain ⟨hweak, hstrict⟩ := hjump i j hij
    change terminalTRank hb g f O L hSupport i +
        frontierTRank g j ≤
      terminalTRank hb g f O L hSupport j +
        frontierTRank g i
    by_cases heq : frontierTRank g i = frontierTRank g j
    · omega
    · have hjumpFront : frontierTRank g i < frontierTRank g j := by
        omega
      have hstrong := hstrict hjumpFront
      rcases hbandI with hi | hi <;> rcases hbandJ with hj | hj <;> omega

/-- In particular strict T-rank increase between EVERY increasing
D₂ target terminal pair suffices for the corrected starred input.
This is a useful stronger, purely target-geometric proof target. -/
theorem target_rank_gaps_of_strict_terminal_ranks
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (L : ForwardQFinalLiteralSignatureTree.SameLiteralForwardSignature
      hb g O)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m + q))
    (hstrict : ∀ i j : MixedProduct.BulletIndex (kind g.core),
      i.1 < j.1 →
        terminalTRank hb g f O L hSupport i <
          terminalTRank hb g f O L hSupport j) :
    TargetRankGapsOrdered hb g f O L hSupport := by
  apply (target_rank_gaps_iff_terminal_rank_jump_order
    hb g f O L hSupport).2
  intro i j hij
  have h := hstrict i j hij
  exact ⟨Nat.le_of_lt h, fun _ => h⟩

end DualTree.ForwardQFinalTargetRankBands
