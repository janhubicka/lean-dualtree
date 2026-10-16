import DualTree.ForwardQFinalSelectedPredecessors
import DualTree.ForwardQFinalRetainedRanks

/-!
# Count the NEW projected predecessors in Lemma 27's final support

Once a coordinate support root z passes the exact final
target-height filter, every proper local root predecessor w
also passes it. By the checked cross-frontier disjointness
and canonical projection prefix reflection, all newly projected
strict predecessors of P_i(z) come from exactly these local w.

The rank contribution of new projected roots is therefore
equal to the intrinsic height of z in its OWN coordinate word's
variable support. This file carries out the finite cardinality
argument using the genuine bounded local root subtype and
projection injectivity; no matching to the old l source
variables is needed or assumed.

The final full rank identity is obtained by adding this count
to the independently checked old retained count
h_T(frontier_i). That addition and the complete-skew
verification belong to the next module.
-/

namespace DualTree.ForwardQFinalProjectedPredecessorCount

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSelectedPredecessors

/-- The genuinely present local variable support roots
strictly preceding z, represented by their bounded node
type (rather than by their projected ambient images). -/
noncomputable def localStrictPredecessors
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    Finset (BoundedNode b (k - (m + 1))) := by
  classical
  exact (f.vector.components i).support.toFinset.filter
    (fun w => IsStrictPrefix w.1 z.1)

/-- No implicit completion of the local support: only
actual variable roots on the strict path to z count. -/
theorem localStrictPredecessors_mem_iff
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z w : BoundedNode b (k - (m + 1))) :
    w ∈ localStrictPredecessors c f i z ↔
      w ∈ (f.vector.components i).support ∧
      IsStrictPrefix w.1 z.1 := by
  classical
  simp [localStrictPredecessors]

/-- Forgetting bounded-node certificates sends the local
strict-root filter EXACTLY onto the strict-predecessor
filter of the actual local support-node list. -/
theorem localStrictPredecessors_value_image_eq
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    (localStrictPredecessors c f i z).image
      (fun w => w.1) =
    ((f.vector.components i).toVariableWord.supportNodes.toFinset.filter
      (fun s => SkewTree.strictPrefixB s z.1 = true)) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨w, hw, hval⟩ := Finset.mem_image.mp hs
    obtain ⟨hws,hpre⟩ :=
      (localStrictPredecessors_mem_iff c f i z w).1 hw
    have hsSupport :
        s ∈ (f.vector.components i).toVariableWord.supportNodes := by
      change s ∈ ((f.vector.components i).support.map
        (fun t => t.1))
      exact List.mem_map.mpr ⟨w,hws,hval⟩
    have hsp : SkewTree.strictPrefixB s z.1 = true := by
      have hsStrict : IsStrictPrefix s z.1 := by
        simpa only [hval] using hpre
      exact (SkewBranchGeometry.strictPrefixB_iff s z.1).2 hsStrict
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hsSupport, hsp⟩
  · intro hs
    obtain ⟨hsSupport, hpre⟩ := Finset.mem_filter.mp hs
    have hsMap :
        s ∈ ((f.vector.components i).support.map
          (fun t => t.1)) :=
      List.mem_toFinset.mp hsSupport
    obtain ⟨w, hwSupport, hval⟩ := List.mem_map.mp hsMap
    have hwStrict : IsStrictPrefix w.1 z.1 := by
      have hsStrict : IsStrictPrefix s z.1 :=
        (SkewBranchGeometry.strictPrefixB_iff s z.1).1 hpre
      simpa only [hval] using hsStrict
    exact Finset.mem_image.mpr
      ⟨w,(localStrictPredecessors_mem_iff c f i z w).2
        ⟨hwSupport,hwStrict⟩,hval⟩

/-- Cardinality of local strict variable roots = the
true INTRINSIC rank in the component's variable support.
The bounded-node forgetful map is injective, so it cannot
identify distinct local variable names. -/
theorem localStrictPredecessors_card_eq_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    (localStrictPredecessors c f i z).card =
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 := by
  classical
  have hmapCard :
      ((localStrictPredecessors c f i z).image
        (fun w => w.1)).card =
      (localStrictPredecessors c f i z).card := by
    apply (Finset.card_image_iff).2
    intro w hw v hv heq
    exact Subtype.ext heq
  have hnodup :
      (f.vector.components i).toVariableWord.supportNodes.Nodup :=
    VariableWord.supportNodes_nodup
      (f.vector.components i).toVariableWord
  calc
    (localStrictPredecessors c f i z).card =
      ((localStrictPredecessors c f i z).image
        (fun w => w.1)).card := hmapCard.symm
    _ = ((f.vector.components i).toVariableWord.supportNodes.toFinset.filter
        (fun s => SkewTree.strictPrefixB s z.1 = true)).card :=
      congrArg Finset.card
        (localStrictPredecessors_value_image_eq c f i z)
    _ = SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 :=
      (ForwardQFinalRetainedRanks.heightAt_nodup_list_eq_card
        (f.vector.components i).toVariableWord.supportNodes
        hnodup z.1).symm

/-- The strict-predecessor filter on ALL selected new
projected roots equals the image of local proper variable
root predecessors. The target rank condition on z is used
ONLY to make the local root filter hereditary. -/
theorem selected_projected_strict_filter_eq_image
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M) :
    ((selectedProjectedRoots c f M).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)) =
    (localStrictPredecessors c f i z).image
      (fun w => (projected c ⟨i,w⟩).1) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hselected,hpreB⟩ := Finset.mem_filter.mp hs
    have hpre : IsStrictPrefix s (projected c ⟨i,z⟩).1 :=
      (SkewBranchGeometry.strictPrefixB_iff _ _).1 hpreB
    obtain ⟨w,hw,hstrict,hsEq⟩ :=
      (selected_new_predecessor_iff_local_support
        c f M i z hz s).1 ⟨hselected,hpre⟩
    exact Finset.mem_image.mpr
      ⟨w,(localStrictPredecessors_mem_iff c f i z w).2
        ⟨hw,hstrict⟩,hsEq.symm⟩
  · intro hs
    obtain ⟨w,hw,hsEq⟩ := Finset.mem_image.mp hs
    obtain ⟨hwSupport,hpre⟩ :=
      (localStrictPredecessors_mem_iff c f i z w).1 hw
    have hselected :
        s ∈ selectedProjectedRoots c f M ∧
        IsStrictPrefix s (projected c ⟨i,z⟩).1 :=
      (selected_new_predecessor_iff_local_support
        c f M i z hz s).2
          ⟨w,hwSupport,hpre,hsEq.symm⟩
    exact Finset.mem_filter.mpr
      ⟨hselected.1,
        (SkewBranchGeometry.strictPrefixB_iff _ _).2
          hselected.2⟩

/-- EXACT new-root predecessor count at P_i(z).
This is the second summand of the final intrinsic rank:
the local component intrinsic height, NOT its ambient
T-rank or the cardinality of old Q source variables. -/
theorem selected_projected_predecessor_card_eq_local_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hz : (⟨i,z⟩ : LocalAddress c) ∈
      selectedLocalRoots c f M) :
    ((selectedProjectedRoots c f M).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)).card =
    SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 := by
  classical
  have hcard :
      ((localStrictPredecessors c f i z).image
        (fun w => (projected c ⟨i,w⟩).1)).card =
      (localStrictPredecessors c f i z).card := by
    apply (Finset.card_image_iff).2
    intro w hw v hv heq
    exact projectLocal_injective c i (Subtype.ext heq)
  calc
    ((selectedProjectedRoots c f M).filter
      (fun s => SkewTree.strictPrefixB s
        (projected c ⟨i,z⟩).1 = true)).card =
      ((localStrictPredecessors c f i z).image
        (fun w => (projected c ⟨i,w⟩).1)).card :=
      congrArg Finset.card
        (selected_projected_strict_filter_eq_image c f M i z hz)
    _ = (localStrictPredecessors c f i z).card := hcard
    _ = SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 :=
      localStrictPredecessors_card_eq_height c f i z

end DualTree.ForwardQFinalProjectedPredecessorCount
