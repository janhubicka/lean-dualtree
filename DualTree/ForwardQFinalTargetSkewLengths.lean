import DualTree.ForwardQFinalTargetIntrinsicBands
import DualTree.ForwardQFinalCrossBandLex
import DualTree.SupportReachability
import DualTree.SkewLevelOrder

/-!
# Recover the source D₂ ordering from the actual target's skew length axioms

The target has exactly the same Q support as the reconstructed raw
mixed point, but its own semi-complete skew proof is stronger than
mere equality of node sets. The target's intrinsic rank at each
chosen terminal is already certified to match the original source
T-frontier band (m or m+1).

For two increasing sorted source D₂ indices:
* if the frontier T-ranks agree, the projected cones are ordered in
  ordinary lex, the TARGET terminals have equal target-intrinsic
  ranks, and skew clause II yields nondecreasing terminal lengths;
* if the frontier T-rank jumps from m to m+1, the TARGET terminal
  intrinsic rank strictly increases, and skew clause III yields
  STRICTLY increasing terminal lengths. In ordinary lex the high-band
  cone instead lies before the low-band cone.

Neither deduction presupposes that the selected target D₂ tails are
already starred. These are the precise target-side skew inequalities
needed to establish the previously outstanding admissibility order.
-/

namespace DualTree.ForwardQFinalTargetSkewLengths

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetRankGap
open ForwardQFinalTargetRankBands
open ForwardQFinalTargetIntrinsicBands
open ForwardQFinalTargetD2MixedPoint

/-- The target terminal at each original D₂ marker is an actual
vertex of the target starred tree, independently of ordinary
mixed-coordinate letter values. -/
theorem target_terminal_mem_O
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i : MixedProduct.BulletIndex (kind g.core)) :
    targetTerminalAtBullet hb g f O L hSupport i ∈ O.tree := by
  rw [← targetMixedPoint_projection_eq_targetTerminal
    hb g f O L hSupport fallback σ i]
  exact ForwardQFinalTargetTreeEquality.targetMixedPoint_markedProjection_mem_target
    hb g f O L hSupport fallback σ i

/-- Distinct selected source D₂ indices never reconstruct the
same target terminal, by genuine disjointness of the minimal
complete-T frontier cones. -/
theorem target_terminals_ne
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1) :
    targetTerminalAtBullet hb g f O L hSupport i ≠
      targetTerminalAtBullet hb g f O L hSupport j := by
  intro heq
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hp : markedProjection g.core x i =
      markedProjection g.core x j := by
    apply Subtype.ext
    calc
      (markedProjection g.core x i).1 =
        targetTerminalAtBullet hb g f O L hSupport i :=
          targetMixedPoint_projection_eq_targetTerminal
            hb g f O L hSupport fallback σ i
      _ = targetTerminalAtBullet hb g f O L hSupport j := heq
      _ = (markedProjection g.core x j).1 :=
          (targetMixedPoint_projection_eq_targetTerminal
            hb g f O L hSupport fallback σ j).symm
  have heqidx := (markedProjection_injective g.core x) hp
  exact (ne_of_lt hij) (congrArg Subtype.val heqidx)

/-- For any two distinct reconstructed target terminals, the
target's own semi-complete skew predicate supplies both printed
numerical skew length clauses II and III. Singleton skewness is
excluded using the actual two distinct target vertices. -/
theorem target_skew_II_III_at_pair
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1) :
    SkewTree.condIIB O.tree = true ∧
      SkewTree.condIIIB O.tree = true := by
  have hi := target_terminal_mem_O
    hb g f O L hSupport fallback σ i
  have hj := target_terminal_mem_O
    hb g f O L hSupport fallback σ j
  have hne := target_terminals_ne
    hb g f O L hSupport fallback σ i j hij
  have hnon : O.tree.length ≠ 1 :=
    SupportReachability.nonsingleton_of_distinct_members
      O.tree hi hj hne
  have hs := O.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hs
  have hk := hs.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hk
  have hr := hk.2
  simp [Bool.and_eq_true] at hr
  rcases hr with hone | hrest
  · exact (hnon hone).elim
  · exact ⟨hrest.1.1.2, hrest.1.2⟩

/-- At equal complete-T source frontier ranks, the terminals
of the genuine TARGET are ordered in ordinary lex by the sorted
source D₂ indices, regardless of their selected local tail depths. -/
theorem target_terminal_lex_same_frontier_rank
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1)
    (hfront : frontierTRank g i = frontierTRank g j) :
    FinLexLE
      (targetTerminalAtBullet hb g f O L hSupport i)
      (targetTerminalAtBullet hb g f O L hSupport j) := by
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hlex :=
    ForwardQFinalCrossBandLex.projected_lex_of_same_frontier_rank_index_lt
      g.core i.1 j.1 hij hfront
      (targetBulletPoint hb g f O L hSupport i)
      (targetBulletPoint hb g f O L hSupport j)
  change FinLexLE (markedProjection g.core x i).1
    (markedProjection g.core x j).1 at hlex
  rw [targetMixedPoint_projection_eq_targetTerminal
      hb g f O L hSupport fallback σ i,
    targetMixedPoint_projection_eq_targetTerminal
      hb g f O L hSupport fallback σ j] at hlex
  exact hlex

/-- When a pair of source frontiers crosses from T rank m
to m+1, the actual target terminals are in REVERSE ordinary
lex order: high-band target terminal first. -/
theorem target_terminal_lex_high_before_low
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hi : frontierTRank g i = m)
    (hj : frontierTRank g j = m + 1) :
    FinLexLE
      (targetTerminalAtBullet hb g f O L hSupport j)
      (targetTerminalAtBullet hb g f O L hSupport i) := by
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hlex :=
    ForwardQFinalCrossBandLex.projected_rank_succ_lex_before_rank_m
      g.core i.1 j.1 hi hj
      (targetBulletPoint hb g f O L hSupport i)
      (targetBulletPoint hb g f O L hSupport j)
  change FinLexLE (markedProjection g.core x j).1
    (markedProjection g.core x i).1 at hlex
  rw [targetMixedPoint_projection_eq_targetTerminal
      hb g f O L hSupport fallback σ j,
    targetMixedPoint_projection_eq_targetTerminal
      hb g f O L hSupport fallback σ i] at hlex
  exact hlex

/-- The ACTUAL target's skew clause II gives weakly increasing
terminal word lengths within each source T-frontier rank band. -/
theorem target_terminal_length_le_same_frontier_rank
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1)
    (hfront : frontierTRank g i = frontierTRank g j) :
    (targetTerminalAtBullet hb g f O L hSupport i).length ≤
      (targetTerminalAtBullet hb g f O L hSupport j).length := by
  let ti := targetTerminalAtBullet hb g f O L hSupport i
  let tj := targetTerminalAtBullet hb g f O L hSupport j
  have hII :=
    (target_skew_II_III_at_pair
      hb g f O L hSupport fallback σ i j hij).1
  have hcell :=
    (List.all_eq_true.mp
      ((show SkewTree.condIIB O.tree = true from hII))) ti
        (target_terminal_mem_O hb g f O L hSupport fallback σ i)
  have hentry := (List.all_eq_true.mp hcell) tj
    (target_terminal_mem_O hb g f O L hSupport fallback σ j)
  have hrank :
      SkewTree.heightAt O.tree ti = SkewTree.heightAt O.tree tj :=
    (target_O_rank_eq_iff_frontier_T_rank_eq
      hb g f O L hSupport fallback σ i j).2 hfront
  have hlex : FinLexLE ti tj :=
    target_terminal_lex_same_frontier_rank
      hb g f O L hSupport fallback σ i j hij hfront
  change
    (if SkewTree.heightAt O.tree ti = SkewTree.heightAt O.tree tj ∧
        FinLexLE ti tj then decide (ti.length ≤ tj.length)
     else true) = true at hentry
  simpa [hrank, hlex] using hentry

/-- Across an increase of source frontier T rank, the
ACTUAL target's skew clause III forces a STRICT increase
of terminal word lengths, without assuming any starred
order of the selected local tails. -/
theorem target_terminal_length_lt_frontier_jump
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
    (fallback : α)
    (σ : ForwardQFinalGlobalFibreSubstitution.FinalRoot g f → α)
    (i j : MixedProduct.BulletIndex (kind g.core))
    (hij : i.1 < j.1)
    (hfront : frontierTRank g i < frontierTRank g j) :
    (targetTerminalAtBullet hb g f O L hSupport i).length <
      (targetTerminalAtBullet hb g f O L hSupport j).length := by
  let ti := targetTerminalAtBullet hb g f O L hSupport i
  let tj := targetTerminalAtBullet hb g f O L hSupport j
  have hIII :=
    (target_skew_II_III_at_pair
      hb g f O L hSupport fallback σ i j hij).2
  have hrow := (List.all_eq_true.mp hIII) ti
    (target_terminal_mem_O hb g f O L hSupport fallback σ i)
  have hcell := (List.all_eq_true.mp hrow) tj
    (target_terminal_mem_O hb g f O L hSupport fallback σ j)
  have hrank :
      SkewTree.heightAt O.tree ti < SkewTree.heightAt O.tree tj :=
    (target_O_rank_lt_iff_frontier_T_rank_lt
      hb g f O L hSupport fallback σ i j).2 hfront
  change
    (if SkewTree.heightAt O.tree ti < SkewTree.heightAt O.tree tj
     then decide (ti.length < tj.length) else true) = true at hcell
  simpa [hrank] using hcell

end DualTree.ForwardQFinalTargetSkewLengths
