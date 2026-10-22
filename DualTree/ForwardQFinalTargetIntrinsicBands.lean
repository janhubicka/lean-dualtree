import DualTree.ForwardQFinalTargetRankBands
import DualTree.ForwardQFrontierBandMatch
import DualTree.ForwardQFinalRetainedRanks

/-!
# Intrinsic ranks of genuine target terminals versus source frontier bands

The target-selected mixed point reconstructed in Lemma 27 has an
exact corrected Q node SET equal to the target O.tree.toFinset.
To use O's own skew axioms we must show explicitly that the intrinsic
rank is independent of the enumeration of that finite support.

The existing Q-to-T frontier band theorem then proves that the
ACTUAL target O terminal at a selected source D2 index i lies at
intrinsic target rank h_O(cut) or h_O(cut)+1 according as the original
minimal complete-T frontier rank equals m or m+1.

This is an exact geometric bridge, independent of any D2 starred
order. It does not yet use the skew length clauses of O to deduce
the target terminal ambient T-rank inequalities.
-/

namespace DualTree.ForwardQFinalTargetIntrinsicBands

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalTargetRankGap
open ForwardQFinalTargetRankBands
open ForwardQFinalTargetD2MixedPoint

/-- The genuine target's semi-complete skew axiom implies that its
finite support list has no repetitions. -/
theorem target_tree_nodup
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : O.tree.Nodup := by
  have hs := O.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hs
  have hk := hs.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hk
  simpa using hk.1

/-- A finite support's intrinsic predecessor count does not
depend on the enumeration: the actual target O list and the
corrected Q node Finset have the SAME intrinsic rank at every node,
without an unproved list-equality or canonical enumeration. -/
theorem target_heightAt_eq_actual_Q
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
    (t : Node b) :
    SkewTree.heightAt O.tree t =
      SkewTree.heightAt
        (nodes g.core
          (targetMixedPoint hb g f O L hSupport fallback σ)).toList t := by
  classical
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hset : nodes g.core x = O.tree.toFinset :=
    ForwardQFinalTargetTreeEquality.targetMixedPoint_Q_node_set_eq_target
      hb g f O L hSupport fallback σ
  calc
    SkewTree.heightAt O.tree t =
        (O.tree.toFinset.filter
          (fun u => SkewTree.strictPrefixB u t = true)).card :=
      ForwardQFinalRetainedRanks.heightAt_nodup_list_eq_card
        O.tree (target_tree_nodup O) t
    _ = ((nodes g.core x).filter
          (fun u => SkewTree.strictPrefixB u t = true)).card := by
      rw [hset]
    _ = SkewTree.heightAt (nodes g.core x).toList t :=
      (ForwardQFinalRetainedRanks.heightAt_finset_eq_card
        (nodes g.core x) t).symm

/-- The particular target O terminal has the exact low/high
intrinsic rank dictated by its original selected T frontier.
This does NOT assume the selected D2 local point lengths are
ordered or that the target mixed point is starred. -/
theorem target_terminal_O_T_frontier_rank_band
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
    (SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport i) =
        SkewTree.heightAt g.core.source.tree g.core.cut ∧
      frontierTRank g i = m) ∨
    (SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport i) =
        SkewTree.heightAt g.core.source.tree g.core.cut + 1 ∧
      frontierTRank g i = m + 1) := by
  let x := targetMixedPoint hb g f O L hSupport fallback σ
  have hproj :=
    targetMixedPoint_projection_eq_targetTerminal
      hb g f O L hSupport fallback σ i
  have hheight :
      SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport i) =
      SkewTree.heightAt (nodes g.core x).toList
        (markedProjection g.core x i).1 := by
    rw [← hproj]
    exact target_heightAt_eq_actual_Q
      hb g f O L hSupport fallback σ _
  rcases ForwardQFrontierBandMatch.marked_Q_T_frontier_rank_band
      hb g.core x i with hlow | hhigh
  · left
    exact ⟨hheight.trans hlow.1, by
      simpa only [frontierTRank, g.core.hm] using hlow.2⟩
  · right
    exact ⟨hheight.trans hhigh.1, by
      simpa only [frontierTRank, g.core.hm] using hhigh.2⟩

/-- Two actual target terminals have equal target-intrinsic
ranks if and only if their original minimal T frontier ranks
are equal. This holds without D2-starred admissibility. -/
theorem target_O_rank_eq_iff_frontier_T_rank_eq
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
    (i j : MixedProduct.BulletIndex (kind g.core)) :
    (SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport i) =
      SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport j)) ↔
      frontierTRank g i = frontierTRank g j := by
  rcases target_terminal_O_T_frontier_rank_band
      hb g f O L hSupport fallback σ i with hi | hi
  <;> rcases target_terminal_O_T_frontier_rank_band
      hb g f O L hSupport fallback σ j with hj | hj
  <;> constructor <;> intro h <;> omega

/-- Strict target-intrinsic rank comparison is exactly the
original T-frontier band comparison. -/
theorem target_O_rank_lt_iff_frontier_T_rank_lt
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
    (i j : MixedProduct.BulletIndex (kind g.core)) :
    (SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport i) <
      SkewTree.heightAt O.tree
        (targetTerminalAtBullet hb g f O L hSupport j)) ↔
      frontierTRank g i < frontierTRank g j := by
  rcases target_terminal_O_T_frontier_rank_band
      hb g f O L hSupport fallback σ i with hi | hi
  <;> rcases target_terminal_O_T_frontier_rank_band
      hb g f O L hSupport fallback σ j with hj | hj
  <;> constructor <;> intro h <;> omega

end DualTree.ForwardQFinalTargetIntrinsicBands
