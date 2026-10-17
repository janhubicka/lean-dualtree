import DualTree.ForwardCompleteRankPredecessor
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalVectorOrdering
import DualTree.MeetClosedFromBranching

/-!
# Quantitative local rank gaps in the corrected Lemma 27 vector word

The vector-complete axiom separates successive intrinsic levels
between EVERY pair of coordinates. If the second coordinate's
root has rank at least two greater than the first root, truncate
its certified inverse tree address to the intermediate level.
This gives TWO genuinely strict word-length inequalities, hence
a gap of at least two ambient digits.

This is the exact quantitative estimate missing in the reverse
rank-(m+1) / rank-m frontier comparison. The result is stated
for actual components of the local vector Ramsey word, without
assuming skewness of the assembled final support.
-/

namespace DualTree.ForwardQFinalLocalRankGaps

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- A local intrinsic support rank gap of at least two gives
a word-length gap of at least two, for arbitrary coordinates
in the same genuine vector-complete local Ramsey word. -/
theorem local_length_add_two_le_of_rank_gap_two
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z ∈ (f.vector.components i).support)
    (hw : w ∈ (f.vector.components j).support)
    (hgap :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 + 2 ≤
      SkewTree.heightAt
        (f.vector.components j).toVariableWord.supportNodes w.1) :
    z.1.length + 2 ≤ w.1.length := by
  let r := SkewTree.heightAt
    (f.vector.components i).toVariableWord.supportNodes z.1
  let L := (f.vector.components j).toVariableWord.supportNodes
  have hzNode :
      z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  have hwNode : w.1 ∈ L := by
    change w.1 ∈ (f.vector.components j).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  have hgap' : r + 2 ≤ SkewTree.heightAt L w.1 := hgap
  have hmidBound : r + 1 < SkewTree.heightAt L w.1 := by omega
  have hcomplete : SkewTree.completeB SkewTree.forwardAuxB q L = true :=
    ForwardQFinalTwoFrontierBudget.local_component_complete c f j
  obtain ⟨u, hu, huRank, huPre⟩ :=
    ForwardCompleteRankPredecessor.exists_strict_predecessor_at_rank
      L hcomplete w.1 hwNode (r+1) hmidBound
  have huInSupport :
      u ∈ (f.vector.components j).support.map (fun t => t.1) := by
    exact hu
  obtain ⟨v, hv, hvU⟩ := List.mem_map.mp huInSupport
  have hvNode :
      v.1 ∈ (f.vector.components j).toVariableWord.supportNodes := by
    change v.1 ∈ (f.vector.components j).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  have hvRank :
      SkewTree.heightAt
        (f.vector.components j).toVariableWord.supportNodes v.1 =
        r + 1 := by
    rw [hvU]
    exact huRank
  have hvPre : IsStrictPrefix v.1 w.1 := by
    rw [hvU]
    exact huPre
  have hwq :
      SkewTree.heightAt L w.1 < q :=
    ForwardQFinalTwoFrontierBudget.local_component_height_lt_q
      c f j w hw
  have hrlimit : r < q - 1 := by omega
  have hfirst : z.1.length < v.1.length :=
    ForwardQFinalVectorOrdering.local_lengths_lt_of_successive_level
      c f i j r hrlimit z v hzNode hvNode rfl hvRank
  have hsecond : v.1.length < w.1.length :=
    MeetClosedFromBranching.length_lt_of_strictPrefix hvPre
  omega

/-- Strict local intrinsic rank comparison implies strict
word-length comparison across ANY two coordinates, not merely
within a single coordinate. A one-level gap uses the vector
successor axiom; all larger gaps use the preceding two-step
intermediate-ancestor lemma. -/
theorem local_length_lt_of_rank_lt
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z ∈ (f.vector.components i).support)
    (hw : w ∈ (f.vector.components j).support)
    (hlt :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 <
      SkewTree.heightAt
        (f.vector.components j).toVariableWord.supportNodes w.1) :
    z.1.length < w.1.length := by
  let r := SkewTree.heightAt
    (f.vector.components i).toVariableWord.supportNodes z.1
  let s := SkewTree.heightAt
    (f.vector.components j).toVariableWord.supportNodes w.1
  by_cases htwo : r + 2 ≤ s
  · have hgap :
        SkewTree.heightAt
          (f.vector.components i).toVariableWord.supportNodes z.1 + 2 ≤
        SkewTree.heightAt
          (f.vector.components j).toVariableWord.supportNodes w.1 :=
      htwo
    have hlarge :=
      local_length_add_two_le_of_rank_gap_two c f i j z w hz hw hgap
    omega
  · have hsucc : s = r + 1 := by omega
    have hzNode :
        z.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
      change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    have hwNode :
        w.1 ∈ (f.vector.components j).toVariableWord.supportNodes := by
      change w.1 ∈ (f.vector.components j).support.map (fun t => t.1)
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    have hwq :
        s < q :=
      ForwardQFinalTwoFrontierBudget.local_component_height_lt_q
        c f j w hw
    have hrlimit : r < q - 1 := by omega
    exact ForwardQFinalVectorOrdering.local_lengths_lt_of_successive_level
      c f i j r hrlimit z w hzNode hwNode rfl hsucc

end DualTree.ForwardQFinalLocalRankGaps
