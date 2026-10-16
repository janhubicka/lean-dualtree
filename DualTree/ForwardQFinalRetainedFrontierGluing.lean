import DualTree.ForwardQFinalRetainedEdges
import DualTree.ForwardQFinalRetainedRanks
import DualTree.ForwardQFinalLocalRoots
import DualTree.ForwardQFinalIntrinsicRank
import DualTree.ImmediateSupportHeight

/-!
# Retained/new immediate edge gluing via the EXACT intrinsic rank formula

Suppose s is retained at/before the inclusive corrected cut
in the original complete ambient T, and the genuine sorted
minimal outside-cut frontier t_i is an immediate T-support
successor of s. The final T'_M includes selected projected
local variable roots P_i(z); let z_i be the genuine root
of the post-Ramsey local coordinate support f_i.

The local intrinsic rank of z_i is zero, so the checked
exact final-support height formula gives

    height_(T'_M)(P_i(z_i)) = height_T(t_i).

Since t_i is immediate above retained s in T,
    height_T(t_i) = height_T(s) + 1.
The separately verified retained-height invariance gives
    height_T(s) = height_(T'_M)(s).

Thus, whenever P_i(z_i) is selected by the target-M cutoff,
its final intrinsic rank is exactly one larger than s.
Because s prefixes t_i and t_i prefixes P_i(z_i),
the generic strict-prefix/rank-gap criterion proves that
s -> P_i(z_i) is an IMMEDIATE support edge in the FULL T'_M.

The exact first ambient direction from s also persists
by the ordinary ambient prefix transitivity:
  s+[dir] prefix t_i prefix P_i(z_i).

This method avoids an unnecessary direct case analysis of
every intermediate old/new vertex. The remaining branching
proof must locate the sorted frontier coordinate i for
every ambient T edge leaving the retained cut and verify
selection of its local root at the two possible rank levels.
The global M-complete skew theorem and final f' word
remain separate obligations.
-/

namespace DualTree.ForwardQFinalRetainedFrontierGluing

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalLocalRoots

/-- The selected projection of the genuine local root has
final intrinsic rank exactly that of its ambient T frontier.
The extra local summand vanishes because the root has rank 0. -/
theorem projected_localRoot_final_height_eq_frontier
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (hselected :
      (⟨i,localRoot c f i⟩ : LocalAddress c) ∈
        selectedLocalRoots c f M) :
    SkewTree.heightAt (finalBudgetSupport c f M).toList
      (projected c ⟨i,localRoot c f i⟩).1 =
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  rw [ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i (localRoot c f i) hselected,
    localRoot_height_zero c f i]
  simp

/-- If a retained vertex s has immediate T-successor the
frontier t_i and its genuine local root is M-selected, then
the projection P_i(z_i) REPLACES the outside-cut edge as an
immediate edge of the ENTIRE assembled T'_M support.

The proof uses only the true final intrinsic rank equation,
rank preservation on retained vertices and support prefix
geometry. It never assumes an ambient one-letter edge. -/
theorem retained_frontier_localRoot_is_final_immediate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (hstep : SkewTree.immediateSuccB c.T s
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = true)
    (hselected :
      (⟨i,localRoot c f i⟩ : LocalAddress c) ∈
        selectedLocalRoots c f M) :
    SkewTree.immediateSuccB
      (finalBudgetSupport c f M).toList
      s (projected c ⟨i,localRoot c f i⟩).1 = true := by
  classical
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  let x := (projected c ⟨i,localRoot c f i⟩).1
  let S := (finalBudgetSupport c f M).toList
  have hsFinal : s ∈ S := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_union.mpr (Or.inl hs)
  have hxFinal : x ∈ S := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_union.mpr
    exact Or.inr
      (Finset.mem_image.mpr
        ⟨⟨i,localRoot c f i⟩,hselected,rfl⟩)
  have hT :=
    (SkewBranchGeometry.immediateSuccB_iff c.T s t).1 hstep
  have hpre : IsPrefix s x :=
    isPrefix_trans hT.2.1.1
      (projected_cone c ⟨i,localRoot c f i⟩)
  have hneq : s ≠ x := by
    intro heq
    have hsBefore : ForwardAux s c.cut :=
      (Finset.mem_filter.mp hs).2
    have hxBefore : ForwardAux x c.cut := by
      rw [← heq]
      exact hsBefore
    exact (projected_outside_cut
      c ⟨i,localRoot c f i⟩) hxBefore
  have hstrict : IsStrictPrefix s x := ⟨hpre,hneq⟩
  have hrankT : SkewTree.heightAt c.T t =
      SkewTree.heightAt c.T s + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      c.T s t (ForwardQFinalRetainedRanks.ambientT_nodup c)
      (retained_subset_T c s hs) hstep
  have hrankOld : SkewTree.heightAt S s =
      SkewTree.heightAt c.T s :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs
  have hrankNew : SkewTree.heightAt S x =
      SkewTree.heightAt c.T t :=
    projected_localRoot_final_height_eq_frontier
      c f M i hselected
  have hgap : SkewTree.heightAt S x =
      SkewTree.heightAt S s + 1 := by
    rw [hrankNew,hrankT,hrankOld]
  exact ForwardQFinalProjectedFullDirections.immediate_of_rank_succ
    S s x hsFinal hxFinal hstrict hgap

/-- The replacement immediate edge occupies exactly the
ambient first direction of its original crossing T edge.
This completes the genuine direction-labelled old/new
transition, conditional only on having identified a
frontier index i with a selected local root. -/
theorem retained_frontier_localRoot_immediate_in_direction
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (hstep : SkewTree.immediateSuccB c.T s
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = true)
    (hselected :
      (⟨i,localRoot c f i⟩ : LocalAddress c) ∈
        selectedLocalRoots c f M)
    (dir : Fin b)
    (hdir : IsPrefix (s ++ [dir])
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1) :
    SkewTree.immediateSuccB
      (finalBudgetSupport c f M).toList
      s (projected c ⟨i,localRoot c f i⟩).1 = true ∧
    IsPrefix (s ++ [dir])
      (projected c ⟨i,localRoot c f i⟩).1 := by
  refine ⟨retained_frontier_localRoot_is_final_immediate
      c f M s hs i hstep hselected,?_⟩
  exact isPrefix_trans hdir
    (projected_cone c ⟨i,localRoot c f i⟩)

end DualTree.ForwardQFinalRetainedFrontierGluing
