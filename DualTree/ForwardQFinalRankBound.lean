import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ForwardFrontierRanks

/-!
# Every vertex of the corrected final T'_M lies below target rank M

The exact intrinsic-height formula for the NEW projected
vertices proves their T'_M heights are below M by the
original printed rank-budget filter.

The RETAINED vertices need a separate argument:
they are all at or before the corrected inclusive forward
cut t0 in the original complete skew support T. The checked
forward-order/rank theorem therefore gives their ambient
intrinsic ranks <= h_T(t0)=m. Their ranks are unchanged in
the full final support. Hence under the necessary numerical
hypothesis m < M every retained vertex also has rank < M.

The combination establishes a UNIFORM height bound on
the full final support, including both its old and new
parts. This is a genuine step toward M-completeness but
does NOT prove full b-branching, or the global skew
length-order axioms, or construct the ambient f'.
-/

namespace DualTree.ForwardQFinalRankBound

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- An old complete-support T vertex at/before the
corrected forward cut cannot have intrinsic T rank
larger than the distinguished cut's rank m. -/
theorem retained_T_rank_le_cut_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ retained c) :
    SkewTree.heightAt c.T t ≤ m := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have haux : ForwardAux t c.cut :=
    (Finset.mem_filter.mp ht).2
  have hle :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.T hc.1 c.hnon
      (retained_subset_T c t ht) c.hcutT haux
  simpa only [c.hm] using hle

/-- Even after all local new projected roots have been
added, a retained vertex still has rank at most m. -/
theorem retained_final_rank_le_cut_rank
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b)
    (ht : t ∈ retained c) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList t ≤ m := by
  rw [ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
    c f M t ht]
  exact retained_T_rank_le_cut_rank c t ht

/-- Every old retained vertex has final intrinsic rank
below target M once M is STRICTLY ABOVE the earlier
source-cut rank m. This numerical hypothesis is real;
it cannot simply be dropped for arbitrary M. -/
theorem retained_final_rank_lt_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (hM : m < M)
    (t : Node b)
    (ht : t ∈ retained c) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList t < M :=
  lt_of_le_of_lt
    (retained_final_rank_le_cut_rank c f M t ht) hM

/-- ALL vertices of the exact target-height-filtered
candidate final support, old OR new, lie at actual
intrinsic T'_M rank < M, assuming m<M.
This conclusion is about the genuine assembled support
rank, not the easier ambient T-rank. -/
theorem finalBudgetSupport_all_heights_lt_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (hM : m < M)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList t < M := by
  classical
  change t ∈ retained c ∪ selectedProjectedRoots c f M at ht
  rcases Finset.mem_union.mp ht with hret | hnew
  · exact retained_final_rank_lt_target c f M hM t hret
  · exact
      ForwardQFinalIntrinsicRank.final_all_selected_projected_heights_lt_target
        c f M t hnew

end DualTree.ForwardQFinalRankBound
