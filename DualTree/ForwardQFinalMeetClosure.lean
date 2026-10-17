import DualTree.ForwardQFinalExactBranching
import DualTree.ForwardCompleteEmbedding
import DualTree.ForwardInclusiveFrontier
import DualTree.MeetClosedFromBranching

/-!
# Root and ambient meet closure of the final corrected Lemma 27 support

The exact final support T'_M is a subset of the complete
ambient support T and contains the entire initial
forward-auxiliary cut, including the distinguished cut t0.

The genuine forward-complete support root r of T prefixes
t0 and therefore lies at/before the inclusive cut. It
belongs to the final retained support and prefixes EVERY
vertex of the final support, since that is a subset of T.
Hence the Boolean rootedB predicate holds on T'_M.

The preceding formalization already proved
AtMostOneDirection for every vertex of the assembled
support, by separate retained- and projected-parent
converse arguments. A general independently verified
lemma says that any rooted support with at most one
immediate successor in each direction is ambient
MEET-CLOSED.

We therefore obtain ambient meet closure for the ACTUAL
rank-filtered T'_M without assuming it as an axiom or
inferring it from abstract prefix order alone.

This is a key piece of the skew geometry, but it does
not yet establish the global condIIB/condIIIB ambient
length ordering or the correct special branching
witness condition condIVB of the repaired skew class.
The final ambient variable word f' is still open.
-/

namespace DualTree.ForwardQFinalMeetClosure

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalExactBranching

/-- The actual unique common root of the ambient
forward-complete T belongs to every target-height
filtered final support, since it precedes the cut. -/
theorem ambient_root_mem_final
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    ForwardCompleteEmbedding.rootOf c.T c.hcomplete c.hnon ∈
      (finalBudgetSupport c f M).toList := by
  classical
  let r := ForwardCompleteEmbedding.rootOf
    c.T c.hcomplete c.hnon
  have hrT : r ∈ c.T :=
    ForwardCompleteEmbedding.rootOf_mem
      c.T c.hcomplete c.hnon
  have hpre : IsPrefix r c.cut :=
    ForwardCompleteEmbedding.rootOf_prefix
      c.T c.hcomplete c.hnon c.cut c.hcutT
  have hrCut : ForwardAux r c.cut :=
    ForwardInclusiveFrontier.forwardAux_of_prefix
      hpre (CanonicalForwardAuxIso.forwardAux_refl c.cut)
  have hrRet : r ∈ retained c := by
    unfold retained
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hrT,hrCut⟩
  apply Finset.mem_toList.mpr
  exact Finset.mem_union.mpr (Or.inl hrRet)

/-- The ambient T root remains a common prefix of EVERY
selected final-support node, including the new projections
and the old retained initial part. -/
theorem ambient_root_prefix_final
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (t : Node b)
    (ht : t ∈ (finalBudgetSupport c f M).toList) :
    IsPrefix
      (ForwardCompleteEmbedding.rootOf c.T c.hcomplete c.hnon) t := by
  have htT : t ∈ c.T :=
    finalBudgetSupport_subset_T c f M t
      (Finset.mem_toList.mp ht)
  exact ForwardCompleteEmbedding.rootOf_prefix
    c.T c.hcomplete c.hnon t htT

/-- The actual rank-filtered final T'_M has a genuine
common support root, and its executable rootedB test is
true for EVERY target height M, without a branching
or skewness assumption on the joined final support. -/
theorem final_rootedB
    {b n l k m q M : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    SkewTree.rootedB (finalBudgetSupport c f M).toList = true := by
  let r := ForwardCompleteEmbedding.rootOf
    c.T c.hcomplete c.hnon
  unfold SkewTree.rootedB
  apply List.any_eq_true.mpr
  refine ⟨r,ambient_root_mem_final c f,?_⟩
  apply List.all_eq_true.mpr
  intro t ht
  exact SkewBranchGeometry.isPrefixOf_true_of_prefix
    (ambient_root_prefix_final c f t ht)

/-- The full final support T'_(m+q) is ambient MEET-CLOSED.
Unlike a premature appeal to complete-skewness, this proof
uses the separately established global uniqueness of
immediate directions and the verified common root. -/
theorem final_meetClosed
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    MeetGeometry.MeetClosed
      (finalBudgetSupport c f (m+q)).toList := by
  exact MeetClosedFromBranching.meetClosed_of_rooted_uniqueDirections
    (finalBudgetSupport c f (m+q)).toList
    (final_rootedB c f)
    (final_atMostOneDirection c f)

end DualTree.ForwardQFinalMeetClosure
