import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ImmediateSupportHeight

/-!
# Canonical local roots and nonempty selected frontier cones

A q-complete local variable support is rooted, including its
singleton case. Its unique common prefix root has intrinsic
local rank zero. The previous rank-m/rank-(m+1) budget dichotomy
then gives an ACTUAL selected projected root above:
  * every rank-m frontier;
  * every rank-(m+1) frontier provided 2 <= q.

For q=1 the upper frontiers contribute no projected root,
as the target M=m+1 already makes the old cut a last-level
vertex. This is essential to avoid a spurious branching
assertion in the base case.

These results ensure the appropriate frontier cones are
nonempty; they do not yet prove all support nonleaves
have exactly b immediate directional successors.
-/

namespace DualTree.ForwardQFinalLocalRoots

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalTwoFrontierBudget

/-- A forward q-complete finite support has a common root,
whether it is a singleton or a nonsingleton skew tree. -/
theorem complete_forward_has_root
    {b q : Nat}
    (S : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB q S = true) :
    ∃ root : Node b, root ∈ S ∧
      ∀ t, t ∈ S → IsPrefix root t := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  by_cases hone : S.length = 1
  · cases S with
    | nil =>
        simp at hone
    | cons r rest =>
        cases rest with
        | nil =>
            refine ⟨r,by simp,?_⟩
            intro t ht
            have htr : t = r := by simpa using ht
            subst t
            exact isPrefix_refl r
        | cons u us =>
            simp at hone
  · have hroot : SkewTree.rootedB S = true :=
      CompleteSkewMeet.rootedB_of_skew_nonSingleton
        SkewTree.forwardAuxB S hc.1 hone
    unfold SkewTree.rootedB at hroot
    rcases List.any_eq_true.mp hroot with ⟨r,hr,htest⟩
    refine ⟨r,hr,?_⟩
    intro t ht
    exact DirectionalSupport.prefix_of_isPrefixOf_true
      ((List.all_eq_true.mp htest) t ht)

/-- The local coordinate word's actual bounded support
has a common root; this is not an arbitrarily chosen T
frontier or one of the intermediate Q source roots. -/
theorem exists_local_component_root
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    ∃ z : BoundedNode b (k-(m+1)),
      z ∈ (f.vector.components i).support ∧
      ∀ w : BoundedNode b (k-(m+1)),
        w ∈ (f.vector.components i).support →
          IsPrefix z.1 w.1 := by
  obtain ⟨root,hroot,hprefix⟩ :=
    complete_forward_has_root
      (f.vector.components i).toVariableWord.supportNodes
      (local_component_complete c f i)
  change root ∈ (f.vector.components i).support.map
    (fun t => t.1) at hroot
  rcases List.mem_map.mp hroot with ⟨z,hz,heq⟩
  refine ⟨z,hz,?_⟩
  intro w hw
  have hwNode :
      w.1 ∈ (f.vector.components i).toVariableWord.supportNodes := by
    change w.1 ∈ (f.vector.components i).support.map
      (fun t => t.1)
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hp := hprefix w.1 hwNode
  simpa only [heq] using hp

/-- Canonically chosen root of the ACTUAL local component
variable support in the coordinate's bounded word type. -/
noncomputable def localRoot
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) : BoundedNode b (k-(m+1)) :=
  Classical.choose (exists_local_component_root c f i)

theorem localRoot_mem
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    localRoot c f i ∈ (f.vector.components i).support :=
  (Classical.choose_spec (exists_local_component_root c f i)).1

theorem localRoot_prefix
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (w : BoundedNode b (k-(m+1)))
    (hw : w ∈ (f.vector.components i).support) :
    IsPrefix (localRoot c f i).1 w.1 :=
  (Classical.choose_spec (exists_local_component_root c f i)).2 w hw

/-- Every coordinate's chosen genuine support root
has intrinsic rank ZERO, not merely the rank of
the ambient frontier from which it will be projected. -/
theorem localRoot_height_zero
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes
      (localRoot c f i).1 = 0 := by
  apply ImmediateSupportHeight.heightAt_root_zero
  intro t ht
  change t ∈ (f.vector.components i).support.map
    (fun w => w.1) at ht
  rcases List.mem_map.mp ht with ⟨w,hw,heq⟩
  have hp := localRoot_prefix c f i w hw
  simpa only [heq] using hp

/-- Every rank-m frontier receives at least one ACTUAL
selected new projected root: the genuine local root of f_i. -/
theorem rank_m_frontier_has_selected_root
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m) :
    (projected c ⟨i,localRoot c f i⟩).1 ∈
      selectedProjectedRoots c f (m+q) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨i,localRoot c f i⟩,?_,rfl⟩
  exact selected_of_rank_m_frontier c f i
    (localRoot c f i) hfront (localRoot_mem c f i)

/-- Every rank-(m+1) frontier also receives an ACTUAL
selected new projected root when q>=2.
For q=1 that claim is false by the exact rank cutoff. -/
theorem rank_succ_frontier_has_selected_root_of_two_le_q
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m+1)
    (hq : 2 ≤ q) :
    (projected c ⟨i,localRoot c f i⟩).1 ∈
      selectedProjectedRoots c f (m+q) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨i,localRoot c f i⟩,?_,rfl⟩
  apply (selected_rank_succ_iff c f i
    (localRoot c f i) hfront).2
  refine ⟨localRoot_mem c f i,?_⟩
  rw [localRoot_height_zero c f i]
  omega

end DualTree.ForwardQFinalLocalRoots
