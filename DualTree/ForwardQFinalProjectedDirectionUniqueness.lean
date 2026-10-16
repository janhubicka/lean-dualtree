import DualTree.ForwardQFinalProjectionDirectionReflect
import DualTree.ForwardQFinalProjectedChildConverse
import DualTree.ForwardInclusiveFrontier
import DualTree.MeetClosedDirectionConverse

/-!
# At most one immediate final successor per direction from PROJECTED roots

The final Lemma 27 support T'_M includes selected projections of
q-complete local variable supports. The preceding converse proves
that EVERY immediate final child of a selected projected P_i(z)
comes from a genuine immediate local support child w in the SAME
coordinate i, with the exact projected image.

The preceding labelled-direction equivalence proves that if
P_i(w) belongs to the dir cone above P_i(z), then w belongs
to the SAME dir cone above z. Thus any two competing final
immediate children in one direction correspond to two
competing LOCAL immediate children in that direction.

A local q-complete forward-skew support with an immediate child
is necessarily nonsingleton and is ambient meet-closed; by the
independently verified converse of meet-closure, it has at
most one immediate support child in any given ambient direction.

This proves AT MOST ONE direction-labelled final support
immediate successor for EACH selected projected parent,
independently of its target-height budget rank. Existence
from the mixed Ramsey construction is checked separately.

Retained-parent uniqueness, the global complete-skew order
clauses and the final ambient word f' remain open.
-/

namespace DualTree.ForwardQFinalProjectedDirectionUniqueness

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalProjectedChildConverse

/-- Any two immediate full T'_M successors of the selected
projected parent P_i(z) that occupy the same literal ambient
first direction are EQUAL. The proof makes no complete-skew
assumption on the assembled support and uses only its
verified child classification and the local complete support. -/
theorem selected_projected_atMostOneDirection
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k-(m+1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M)
    (dir : Fin b)
    (x y : Node b)
    (hx : x ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 dir)
    (hy : y ∈ SkewTree.branchWitnesses
      (finalBudgetSupport c f M).toList
      (projected c ⟨i,z⟩).1 dir) :
    x = y := by
  classical
  let L := (f.vector.components i).toVariableWord.supportNodes
  let S := (finalBudgetSupport c f M).toList
  have hdataX :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      S (projected c ⟨i,z⟩).1 x dir).1 hx
  have hdataY :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      S (projected c ⟨i,z⟩).1 y dir).1 hy
  obtain ⟨w,hw,hlocalX,hxEq⟩ :=
    selected_final_immediate_child_is_local_immediate
      c f M i z hz x hdataX.1
  obtain ⟨v,hv,hlocalY,hyEq⟩ :=
    selected_final_immediate_child_is_local_immediate
      c f M i z hz y hdataY.1
  have hzTag :
      (⟨i,z⟩ : LocalAddress c) ∈
        taggedLocalRoots c f :=
    ((selectedLocalRoots_mem_iff c f M ⟨i,z⟩).1 hz).1
  have hzSupp : z ∈ (f.vector.components i).support :=
    (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
      c f i z).1 hzTag
  have hzL : z.1 ∈ L := by
    change z.1 ∈ (f.vector.components i).support.map
      (fun u => u.1)
    exact List.mem_map.mpr ⟨z,hzSupp,rfl⟩
  have hxLocCone :
      IsPrefix (z.1 ++ [dir]) w.1 := by
    apply (ForwardQFinalProjectionDirectionReflect.projected_childCone_iff
      c i z w dir).2
    simpa only [hxEq] using hdataX.2
  have hyLocCone :
      IsPrefix (z.1 ++ [dir]) v.1 := by
    apply (ForwardQFinalProjectionDirectionReflect.projected_childCone_iff
      c i z v dir).2
    simpa only [hyEq] using hdataY.2
  have hxLocalMem :
      w.1 ∈ SkewTree.branchWitnesses L z.1 dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      L z.1 w.1 dir).2 ⟨hlocalX,hxLocCone⟩
  have hyLocalMem :
      v.1 ∈ SkewTree.branchWitnesses L z.1 dir :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      L z.1 v.1 dir).2 ⟨hlocalY,hyLocCone⟩
  have hchildData :=
    (SkewBranchGeometry.immediateSuccB_iff L z.1 w.1).1 hlocalX
  have hnon : L.length ≠ 1 :=
    SupportReachability.nonsingleton_of_distinct_members
      L hzL hchildData.1 hchildData.2.1.2
  have hcomplete : SkewTree.completeB SkewTree.forwardAuxB q L = true :=
    ForwardQFinalTwoFrontierBudget.local_component_complete c f i
  have hmeet : MeetGeometry.MeetClosed L :=
    ForwardInclusiveFrontier.meetClosed_complete_forward
      L hcomplete hnon
  have hunique : MeetClosedFromBranching.AtMostOneDirection L :=
    MeetClosedDirectionConverse.atMostOneDirection_of_meetClosed
      L hmeet
  have heqWV : w.1 = v.1 :=
    hunique z.1 hzL dir w.1 v.1 hxLocalMem hyLocalMem
  have hwv : w = v := Subtype.ext heqWV
  calc
    x = (projected c ⟨i,w⟩).1 := hxEq
    _ = (projected c ⟨i,v⟩).1 := by rw [hwv]
    _ = y := hyEq.symm

end DualTree.ForwardQFinalProjectedDirectionUniqueness
