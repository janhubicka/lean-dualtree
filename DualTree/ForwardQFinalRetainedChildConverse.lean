import DualTree.ForwardQFinalAllDirectionExistence
import DualTree.ForwardQFinalRetainedRanks
import DualTree.ForwardQFinalRetainedFrontierGluing
import DualTree.ForwardQFinalLocalRoots
import DualTree.SupportHeightRanks

/-!
# Converse classification of immediate children of retained T'_M vertices

For directional uniqueness in the final Lemma 27 support,
the previous proofs construct final immediate children from
the original complete T successors. We must also exclude
OTHER immediate final children, not only exhibit a chosen one.

Here are three converse facts:

1. An immediate T'_M edge between retained old vertices
   was already immediate in T. An intermediate ambient T
   node would itself lie before the inclusive cut and hence
   would have survived in T'_M.

2. If an immediate T'_M child of a retained s is instead
   a selected projection P_i(z), then its actual intrinsic
   final rank is one above s. The old frontier lies properly
   above s, and the checked rank equation forces BOTH:
     height_T(frontier_i) = height_T(s) + 1;
     height_ws(f_i)(z) = 0.
   Thus frontier_i is an actual immediate T successor of s.

3. In a q-complete local component support, a genuine
   rank-zero root is UNIQUE: it must equal the common
   localRoot. Hence every projected immediate child of
   a retained vertex is the actual P_i(localRoot_i).

These are the precise uniqueness interfaces at the
retained/new boundary. They do not yet prove the final
at-most-one-direction condition for all vertices.
-/

namespace DualTree.ForwardQFinalRetainedChildConverse

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalLocalRoots

/-- If both endpoints are retained, any immediate edge in
the final filtered T'_M was already an immediate ambient
support edge in the original complete T. -/
theorem retained_final_immediate_is_ambient_immediate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s t : Node b)
    (hs : s ∈ retained c)
    (ht : t ∈ retained c)
    (hstep :
      SkewTree.immediateSuccB (finalBudgetSupport c f M).toList
        s t = true) :
    SkewTree.immediateSuccB c.T s t = true := by
  classical
  obtain ⟨_,hstrict,hno⟩ :=
    (SkewBranchGeometry.immediateSuccB_iff
      (finalBudgetSupport c f M).toList s t).1 hstep
  have htT : t ∈ c.T := retained_subset_T c t ht
  apply (SkewBranchGeometry.immediateSuccB_iff c.T s t).2
  refine ⟨htT,hstrict,?_⟩
  intro u hu hbetween
  have hret : u ∈ retained c :=
    retained_prefix_closed_in_T c u t hu ht hbetween.2.1
  have hfinal : u ∈ (finalBudgetSupport c f M).toList := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_union.mpr (Or.inl hret)
  exact hno u hfinal hbetween

/-- A genuine rank-zero local variable root MUST be the
actual unique common localRoot, even if its bounded address
is not the empty word. -/
theorem local_height_zero_eq_localRoot
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hrank :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 = 0) :
    z = localRoot c f i := by
  let root := localRoot c f i
  let S := (f.vector.components i).toVariableWord.supportNodes
  have hp : IsPrefix root.1 z.1 :=
    localRoot_prefix c f i z hz
  by_cases heq : z = root
  · exact heq
  · have hstrict : IsStrictPrefix root.1 z.1 := by
      refine ⟨hp,?_⟩
      intro hv
      have heqr : root = z := Subtype.ext hv
      exact heq heqr.symm
    have hmem : root.1 ∈ S := by
      change root.1 ∈ (f.vector.components i).support.map
        (fun u => u.1)
      exact List.mem_map.mpr
        ⟨root,localRoot_mem c f i,rfl⟩
    have hlt :
        SkewTree.heightAt S root.1 <
        SkewTree.heightAt S z.1 :=
      SupportHeightRanks.heightAt_lt_of_strictPrefix
        S hmem hstrict
    have hzero : SkewTree.heightAt S root.1 = 0 :=
      localRoot_height_zero c f i
    rw [hzero] at hlt
    have hz0 : SkewTree.heightAt S z.1 = 0 := hrank
    omega

/-- If a selected projection P_i(z) is an immediate child
of a retained final vertex s, then the frontier itself
was an actual immediate T successor of s, and z is
EXACTLY the genuine local component root. -/
theorem retained_final_projected_child_is_frontier_localRoot
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s : Node b)
    (hs : s ∈ retained c)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (hstep :
      SkewTree.immediateSuccB
        (finalBudgetSupport c f M).toList
        s (projected c ⟨i,z⟩).1 = true) :
    SkewTree.immediateSuccB c.T s
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = true ∧
    z = localRoot c f i := by
  classical
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  let p := (projected c ⟨i,z⟩).1
  let S := (finalBudgetSupport c f M).toList
  have hchild :=
    (SkewBranchGeometry.immediateSuccB_iff S s p).1 hstep
  have hpre : IsPrefix s t :=
    (ForwardQFinalBudgetPredecessors.retained_prefix_projected_iff
      c ⟨i,z⟩ s hs).1 hchild.2.1.1
  have hne : s ≠ t := by
    intro heq
    have hbefore : ForwardAux s c.cut :=
      (Finset.mem_filter.mp hs).2
    have hfrontBefore : ForwardAux t c.cut := by
      rw [← heq]
      exact hbefore
    exact (ForwardOrderedProjections.frontierAt_spec
      c.T c.cut i).2.1 hfrontBefore
  have hstrict : IsStrictPrefix s t := ⟨hpre,hne⟩
  have hsT : s ∈ c.T :=
    retained_subset_T c s hs
  have htT : t ∈ c.T :=
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i).1
  have hlt : SkewTree.heightAt c.T s <
      SkewTree.heightAt c.T t :=
    SupportHeightRanks.heightAt_lt_of_strictPrefix
      c.T hsT hstrict
  have hsFinal : s ∈ S := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_union.mpr (Or.inl hs)
  have hFinalNodup : S.Nodup :=
    Finset.nodup_toList (finalBudgetSupport c f M)
  have hgap : SkewTree.heightAt S p =
      SkewTree.heightAt S s + 1 :=
    ImmediateSupportHeight.heightAt_immediate
      S s p hFinalNodup hsFinal hstep
  have hrankOld : SkewTree.heightAt S s =
      SkewTree.heightAt c.T s :=
    ForwardQFinalRetainedRanks.finalBudgetSupport_retained_heightAt_eq_T
      c f M s hs
  have hrankNew : SkewTree.heightAt S p =
      SkewTree.heightAt c.T t +
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 :=
    ForwardQFinalIntrinsicRank.final_projected_height_formula
      c f M i z hz
  have hfrontGap : SkewTree.heightAt c.T t =
      SkewTree.heightAt c.T s + 1 := by
    omega
  have hlocal0 : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = 0 := by
    omega
  have hfrontImm : SkewTree.immediateSuccB c.T s t = true :=
    ForwardQFinalProjectedFullDirections.immediate_of_rank_succ
      c.T s t hsT htT hstrict hfrontGap
  have htag : (⟨i,z⟩ : LocalAddress c) ∈
      taggedLocalRoots c f :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).1
  have hzSupport : z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 htag
  exact ⟨hfrontImm,
    local_height_zero_eq_localRoot c f i z hzSupport hlocal0⟩

end DualTree.ForwardQFinalRetainedChildConverse
