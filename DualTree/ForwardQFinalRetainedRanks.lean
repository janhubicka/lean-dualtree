import DualTree.ForwardQFinalBudgetPredecessors
import DualTree.ImmediateSupportHeight

/-!
# Intrinsic ranks on the retained side of Lemma 27's final support

The exact final ambient support consists of retained T vertices
at or before the inclusive forward cut, plus projected variable
roots satisfying the final target-height cutoff.

We verify:
* every retained vertex has precisely the SAME strict
  predecessor set and intrinsic rank as in the original
  complete ambient support T, even after adding new roots;
* exactly h_T(frontier_i) old retained vertices precede
  any projected root in the i-th frontier cone.

The remaining new-predecessor contribution must be counted
separately before proving the full intrinsic rank formula
h_T'(P_i(z)) = h_T(frontier_i) + h_ws(f_i)(z).
No complete-skew theorem is asserted here.
-/

namespace DualTree.ForwardQFinalRetainedRanks

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalBudgetPredecessors

/-- Intrinsic rank of a finite, duplicate-free Finset support
is the cardinality of its genuine strict-predecessor filter. -/
theorem heightAt_finset_eq_card
    {b : Nat} (S : Finset (Node b)) (t : Node b) :
    SkewTree.heightAt S.toList t =
      (S.filter (fun u => SkewTree.strictPrefixB u t = true)).card := by
  classical
  have hpredNodup : (SkewTree.preds S.toList t).Nodup := by
    unfold SkewTree.preds
    exact (Finset.nodup_toList S).filter _
  have hset : (SkewTree.preds S.toList t).toFinset =
      S.filter (fun u => SkewTree.strictPrefixB u t = true) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_filter,
      ImmediateSupportHeight.mem_preds_iff, Finset.mem_toList,
      SkewBranchGeometry.strictPrefixB_iff]
  calc
    SkewTree.heightAt S.toList t =
        (SkewTree.preds S.toList t).length := rfl
    _ = (SkewTree.preds S.toList t).toFinset.card :=
      (List.toFinset_card_of_nodup hpredNodup).symm
    _ = (S.filter
        (fun u => SkewTree.strictPrefixB u t = true)).card :=
      congrArg Finset.card hset

/-- The same predecessor-cardinality identity for an arbitrary
duplicate-free list support (including the ambient complete T). -/
theorem heightAt_nodup_list_eq_card
    {b : Nat} (S : List (Node b)) (hS : S.Nodup)
    (t : Node b) :
    SkewTree.heightAt S t =
      (S.toFinset.filter
        (fun u => SkewTree.strictPrefixB u t = true)).card := by
  classical
  have hpredNodup : (SkewTree.preds S t).Nodup := by
    unfold SkewTree.preds
    exact hS.filter _
  have hset : (SkewTree.preds S t).toFinset =
      S.toFinset.filter
        (fun u => SkewTree.strictPrefixB u t = true) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_filter,
      ImmediateSupportHeight.mem_preds_iff,
      SkewBranchGeometry.strictPrefixB_iff]
  calc
    SkewTree.heightAt S t = (SkewTree.preds S t).length := rfl
    _ = (SkewTree.preds S t).toFinset.card :=
      (List.toFinset_card_of_nodup hpredNodup).symm
    _ = (S.toFinset.filter
        (fun u => SkewTree.strictPrefixB u t = true)).card :=
      congrArg Finset.card hset

/-- Every complete skew source frame provides a duplicate-free
ambient support; this is part of its checked skew axioms. -/
theorem ambientT_nodup
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) : c.T.Nodup := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  simpa using hskew.1

/-- Strict T-predecessors of an actual outside-cut frontier
are precisely its retained old predecessors. -/
theorem frontier_predecessor_filters_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    (c.T.toFinset.filter
      (fun s => SkewTree.strictPrefixB s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true)) =
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true)) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hT,hpre⟩ := Finset.mem_filter.mp hs
    have hstrict : IsStrictPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
      (SkewBranchGeometry.strictPrefixB_iff _ _).1 hpre
    have hret : s ∈ retained c :=
      ((T_predecessor_frontier_iff_retained c i s
        (List.mem_toFinset.mp hT)).1 hstrict).1
    exact Finset.mem_filter.mpr ⟨hret,hpre⟩
  · intro hs
    obtain ⟨hret,hpre⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (retained_subset_T c s hret),hpre⟩

/-- The exact number of retained old predecessors above any
projected local node P_i(z) is h_T(frontier_i), independent
of z and of the final target height M. -/
theorem frontier_rank_eq_retained_predecessor_card
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true)).card := by
  calc
    SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
      (c.T.toFinset.filter
        (fun s => SkewTree.strictPrefixB s
          (ForwardOrderedProjections.frontierAt
            c.T c.cut i).1 = true)).card :=
      heightAt_nodup_list_eq_card c.T (ambientT_nodup c) _
    _ = ((retained c).filter
      (fun s => SkewTree.strictPrefixB s
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i).1 = true)).card :=
      congrArg Finset.card (frontier_predecessor_filters_eq c i)

/-- Every old predecessor of a retained vertex remains retained:
the inclusive forward cut is prefix-closed within T. -/
theorem retained_predecessor_filters_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ retained c) :
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s t = true)) =
    (c.T.toFinset.filter
      (fun s => SkewTree.strictPrefixB s t = true)) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hret,hpre⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr
        (retained_subset_T c s hret),hpre⟩
  · intro hs
    obtain ⟨hT,hpre⟩ := Finset.mem_filter.mp hs
    have hprefix : IsPrefix s t :=
      ((SkewBranchGeometry.strictPrefixB_iff s t).1 hpre).1
    exact Finset.mem_filter.mpr
      ⟨retained_prefix_closed_in_T c s t
        (List.mem_toFinset.mp hT) ht hprefix,hpre⟩

/-- The retained initial-cut part has exactly the same
intrinsic support rank as T at each retained vertex. -/
theorem retained_heightAt_eq_ambientT
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ retained c) :
    SkewTree.heightAt (retained c).toList t =
      SkewTree.heightAt c.T t := by
  calc
    SkewTree.heightAt (retained c).toList t =
      ((retained c).filter
        (fun s => SkewTree.strictPrefixB s t = true)).card :=
      heightAt_finset_eq_card (retained c) t
    _ = (c.T.toFinset.filter
        (fun s => SkewTree.strictPrefixB s t = true)).card :=
      congrArg Finset.card
        (retained_predecessor_filters_eq c t ht)
    _ = SkewTree.heightAt c.T t :=
      (heightAt_nodup_list_eq_card c.T (ambientT_nodup c) t).symm

/-- A projected new root cannot precede a retained vertex.
Hence the predecessor filter of any retained vertex is
unchanged inside the FINAL filtered support, not only
inside the retained sub-support. -/
theorem final_retained_predecessor_filters_eq
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b) (ht : t ∈ retained c) :
    ((finalBudgetSupport c f M).filter
      (fun s => SkewTree.strictPrefixB s t = true)) =
    ((retained c).filter
      (fun s => SkewTree.strictPrefixB s t = true)) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hsupport,hpre⟩ := Finset.mem_filter.mp hs
    rcases Finset.mem_union.mp hsupport with hret | hnew
    · exact Finset.mem_filter.mpr ⟨hret,hpre⟩
    · obtain ⟨u, _, hnode⟩ := Finset.mem_image.mp hnew
      have hprefix : IsPrefix (projected c u).1 t := by
        rw [hnode]
        exact ((SkewBranchGeometry.strictPrefixB_iff s t).1
          hpre).1
      exact False.elim
        ((projected_not_prefix_retained c u t ht) hprefix)
  · intro hs
    obtain ⟨hret,hpre⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union.mpr (Or.inl hret),hpre⟩

/-- EXACT rank equality for EVERY old retained vertex in
the finished target-filtered support T'_M. The rank is
independent of the mixed Ramsey dimension q and the target
height budget M. -/
theorem finalBudgetSupport_retained_heightAt_eq_T
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b) (ht : t ∈ retained c) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList t =
      SkewTree.heightAt c.T t := by
  calc
    SkewTree.heightAt (finalBudgetSupport c f M).toList t =
      ((finalBudgetSupport c f M).filter
        (fun s => SkewTree.strictPrefixB s t = true)).card :=
      heightAt_finset_eq_card (finalBudgetSupport c f M) t
    _ = ((retained c).filter
        (fun s => SkewTree.strictPrefixB s t = true)).card :=
      congrArg Finset.card
        (final_retained_predecessor_filters_eq c f M t ht)
    _ = SkewTree.heightAt (retained c).toList t :=
      (heightAt_finset_eq_card (retained c) t).symm
    _ = SkewTree.heightAt c.T t :=
      retained_heightAt_eq_ambientT c t ht

end DualTree.ForwardQFinalRetainedRanks
