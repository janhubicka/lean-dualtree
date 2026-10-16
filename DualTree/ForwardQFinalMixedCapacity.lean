import DualTree.ForwardQFinalRetainedFullDirections
import DualTree.CompleteSupportSurjective
import DualTree.ForwardQFinalLocalRoots
import DualTree.ForwardQFinalRetainedRanks

/-!
# The mixed Ramsey dimension is bounded by the actual cone tail height

The ambient complete skew support T has height k. The corrected
inclusive cut has rank m, and the mixed coordinate variable words
live on bounded tails of height h=k-(m+1).

It is tempting to require an EXTRA capacity hypothesis m+q<=k
for the final target M=m+q. In fact the existence of any genuine
q-complete mixed component support in b^{<h} already forces q<=h:
a terminal local support root has intrinsic height q-1,
while the number of strict distinct support prefixes of an
ambient word of length d cannot exceed d. The terminal root
has length <h, hence q<=h and m+q<=k.

The statement is explicitly for a REAL coordinate i.
For an empty coordinate index set the vector-completeness
predicate is vacuous and cannot bound q; later elimination
of the capacity hypothesis will use the fact that the
requested nontrivial branching direction forces a frontier.

No Hall matching, arbitrary-word completion or external
Ramsey principle is used.
-/

namespace DualTree.ForwardQFinalMixedCapacity

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- In a duplicate-free finite support S, the number of strict
support predecessors of any ambient word t cannot exceed
the ambient length of t. Strict prefixes of t have pairwise
different lengths, hence embed into the finite set of
lengths {0,...,|t|-1}. -/
theorem heightAt_le_word_length
    {b : Nat}
    (S : List (Node b))
    (hS : S.Nodup)
    (t : Node b) :
    SkewTree.heightAt S t ≤ t.length := by
  classical
  let P : Finset (Node b) := S.toFinset.filter
    (fun u => SkewTree.strictPrefixB u t = true)
  have hcard : SkewTree.heightAt S t = P.card :=
    ForwardQFinalRetainedRanks.heightAt_nodup_list_eq_card
      S hS t
  have hinj : Set.InjOn (fun u : Node b => u.length)
      (↑P : Set (Node b)) := by
    intro u hu v hv hlength
    have hpu : IsStrictPrefix u t :=
      (SkewBranchGeometry.strictPrefixB_iff u t).1
        (Finset.mem_filter.mp (show u ∈ P from hu)).2
    have hpv : IsStrictPrefix v t :=
      (SkewBranchGeometry.strictPrefixB_iff v t).1
        (Finset.mem_filter.mp (show v ∈ P from hv)).2
    have huv : IsPrefix u v :=
      CutFrontier.prefix_of_prefix_length_le
        hpu.1 hpv.1 (le_of_eq hlength)
    exact CutPreservation.prefix_eq_of_length_eq huv hlength
  have hcardImage :
      (P.image (fun u : Node b => u.length)).card = P.card :=
    (Finset.card_image_iff).2 hinj
  have hsubset :
      P.image (fun u : Node b => u.length) ⊆
        Finset.range t.length := by
    intro n hn
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hn
    have hstrict : IsStrictPrefix u t :=
      (SkewBranchGeometry.strictPrefixB_iff u t).1
        (Finset.mem_filter.mp hu).2
    exact Finset.mem_range.mpr
      (MeetClosedFromBranching.length_lt_of_strictPrefix hstrict)
  calc
    SkewTree.heightAt S t = P.card := hcard
    _ = (P.image (fun u : Node b => u.length)).card :=
      hcardImage.symm
    _ ≤ (Finset.range t.length).card :=
      Finset.card_le_card hsubset
    _ = t.length := Finset.card_range _

/-- A genuine q-complete support inside local bounded word
height h=k-(m+1) forces q<=h. A terminal support root exists
above the genuine local component root, and its local rank
must be exactly q-1. -/
theorem local_dimension_le_common_tail_height
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    q ≤ k-(m+1) := by
  let S := (f.vector.components i).toVariableWord.supportNodes
  have hz : (ForwardQFinalLocalRoots.localRoot c f i).1 ∈ S := by
    change (ForwardQFinalLocalRoots.localRoot c f i).1 ∈
      (f.vector.components i).support.map (fun w => w.1)
    exact List.mem_map.mpr
      ⟨ForwardQFinalLocalRoots.localRoot c f i,
        ForwardQFinalLocalRoots.localRoot_mem c f i,rfl⟩
  obtain ⟨leaf,hleaf,_,hzero⟩ :=
    CompleteSupportSurjective.exists_terminal_above S
      (ForwardQFinalLocalRoots.localRoot c f i).1 hz
  have hcomplete :=
    ForwardQFinalTwoFrontierBudget.local_component_complete c f i
  have hparts := hcomplete
  simp only [SkewTree.completeB,Bool.and_eq_true] at hparts
  have hrow := (List.all_eq_true.mp hparts.2) leaf hleaf
  change
    (if (SkewTree.immediateSuccs S leaf).length = 0 then
      decide (SkewTree.heightAt S leaf + 1 = q)
     else decide ((SkewTree.immediateSuccs S leaf).length = b)) = true
    at hrow
  have hlast : SkewTree.heightAt S leaf + 1 = q := by
    simpa [hzero] using hrow
  have hnodup : S.Nodup :=
    VariableWord.supportNodes_nodup
      (f.vector.components i).toVariableWord
  have hheight : SkewTree.heightAt S leaf ≤ leaf.length :=
    heightAt_le_word_length S hnodup leaf
  have hleafMap : leaf ∈
      (f.vector.components i).support.map (fun z => z.1) := hleaf
  obtain ⟨w,hw,hvalue⟩ := List.mem_map.mp hleafMap
  have hlen : leaf.length < k-(m+1) := by
    rw [← hvalue]
    exact w.2
  omega

/-- Every real mixed coordinate supplies sufficient ambient
complete-support height to contain the final target M=m+q.
The previously explicit numerical capacity bound follows
from the actual typed input rather than an added proof axiom. -/
theorem local_dimension_implies_ambient_capacity
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c) :
    m+q ≤ k := by
  have h := local_dimension_le_common_tail_height c f i
  omega

end DualTree.ForwardQFinalMixedCapacity
