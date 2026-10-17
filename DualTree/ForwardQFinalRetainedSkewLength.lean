import DualTree.ForwardQFinalRetainedRanks
import DualTree.SkewLevelOrder
import DualTree.ForwardProjectedTerminalOrder

/-!
# Global final skew length axioms: the old/old retained case

The corrected Lemma 27 final support T'_M is assembled from an
initial forward-auxiliary cut of a complete ambient T and selected
projected post-Ramsey local variable roots. Its intrinsic ranks
at RETAINED vertices are already proved equal to their ranks in T.

The complete ambient support T satisfies the forward skew
ambient-length conditions (ii) and (iii). Their transfer to
pairs of retained vertices therefore needs NO new branching
or ambient rank argument: simply replace final ranks by the
checked original T ranks, and apply the original skew axioms.

Here we record separately:
* the actual old complete T has corrected forward skewB;
* same-rank retained pairs in forward lex order have
  nondecreasing ambient word lengths;
* increasing intrinsic final ranks at retained vertices
  force STRICTLY increasing ambient word lengths;
* hence lower-rank retained pairs are correctly ordered
  in the forward auxiliary order.

This discharges the retained/retained part of the final
skew clauses II/III. Retained/projected and
projected/projected comparisons remain mathematical
proof obligations, as does the special witness clause IV.
No full skewB assertion for T'_M is made.
-/

namespace DualTree.ForwardQFinalRetainedSkewLength

open ForwardSourceQTree
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalRefinementRoots

/-- A genuine source Frame carries the repaired complete
forward skewB property on its ambient support T. -/
theorem ambient_forward_skew
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.skewB SkewTree.forwardAuxB c.T = true := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  exact hc.1

/-- The old complete support T also satisfies the same-height
forward-lex ambient-length clause II. -/
theorem ambient_condIIB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.condIIB c.T = true := by
  have hs := ambient_forward_skew c
  simp only [SkewTree.skewB, Bool.and_eq_true] at hs
  have hcore := hs.2
  simp [c.hnon, Bool.and_eq_true] at hcore
  exact hcore.1.1.2

/-- If two RETAINED nodes have equal intrinsic ranks
INSIDE THE FINAL assembled T'_M, their ambient word
lengths are nondecreasing when the nodes are in
ordinary forward lexicographic order. -/
theorem final_retained_equal_rank_lex_length_le
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s t : Node b)
    (hs : s ∈ retained c)
    (ht : t ∈ retained c)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s =
      SkewTree.heightAt (finalBudgetSupport c f M).toList t)
    (hlex : FinLexLE s t) :
    s.length ≤ t.length := by
  have hsHeight :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs
  have htHeight :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M t ht
  have hrankT : SkewTree.heightAt c.T s =
      SkewTree.heightAt c.T t := by
    calc
      SkewTree.heightAt c.T s =
          SkewTree.heightAt (finalBudgetSupport c f M).toList s :=
        hsHeight.symm
      _ = SkewTree.heightAt (finalBudgetSupport c f M).toList t :=
        hranks
      _ = SkewTree.heightAt c.T t := htHeight
  have hsRow :=
    (List.all_eq_true.mp (ambient_condIIB c)) s
      (retained_subset_T c s hs)
  have hcell :=
    (List.all_eq_true.mp hsRow) t (retained_subset_T c t ht)
  simpa [hrankT,hlex] using hcell

/-- Strictly increasing FINAL support intrinsic ranks
at retained/retained vertices force strictly increasing
ambient word lengths, by transferring clause III of T. -/
theorem final_retained_lower_rank_length_lt
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s t : Node b)
    (hs : s ∈ retained c)
    (ht : t ∈ retained c)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s <
      SkewTree.heightAt (finalBudgetSupport c f M).toList t) :
    s.length < t.length := by
  have hsHeight :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs
  have htHeight :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M t ht
  have hlt : SkewTree.heightAt c.T s <
      SkewTree.heightAt c.T t := by
    rw [hsHeight,htHeight] at hranks
    exact hranks
  exact SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB (ambient_forward_skew c)
    c.hnon (retained_subset_T c s hs)
    (retained_subset_T c t ht) hlt

/-- The resulting forward auxiliary ordering of old/old
pairs at different intrinsic FINAL heights. -/
theorem final_retained_lower_rank_forwardAux
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (s t : Node b)
    (hs : s ∈ retained c)
    (ht : t ∈ retained c)
    (hranks :
      SkewTree.heightAt (finalBudgetSupport c f M).toList s <
      SkewTree.heightAt (finalBudgetSupport c f M).toList t) :
    ForwardAux s t :=
  Or.inl (final_retained_lower_rank_length_lt
    c f s t hs ht hranks)

end DualTree.ForwardQFinalRetainedSkewLength
