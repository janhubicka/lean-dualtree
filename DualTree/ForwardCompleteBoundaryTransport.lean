import DualTree.ForwardCompleteInitialTransport
import DualTree.ForwardSignatureInteriorPersistence

/-!
# The first boundary survives a change of directional successor

A complete refinement may replace a support successor beyond a retained
cut by a deeper support node. Literal canonical images there need not
stay equal. The new successor nevertheless extends the old successor,
because both lie in the same direction of the original complete support.
Their first ambient boundary at any earlier cut is therefore identical.

The retained-parent interface below derives equality of the old and new
parent ranks from actual canonical address transport. The explicit budget
`heightAt T s + 1 < q` guarantees that the parent remains nonterminal in
the new q-complete support. This hypothesis cannot be dropped when the
refinement is allowed to end at the retained parent.

These are local geometric transport theorems. They neither enumerate
model signatures nor assert stability of an entire transported signature.
-/

namespace DualTree.ForwardCompleteBoundaryTransport

open ForwardCompleteEmbedding ForwardCompleteBijection
open ForwardSignatureBoundary

private theorem successor_prefix_of_subset
    {b k : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonT : T.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (s : Node b) (hs : s ∈ U) (i : Fin b)
    (hbranchU : SkewTree.uniqueBranchB U s i = true) :
    IsPrefix (CanonicalSupportWalk.next T s i)
      (CanonicalSupportWalk.next U s i) := by
  have hnextU := CanonicalSupportWalk.next_unique U s i hbranchU
  have hnextTmem : CanonicalSupportWalk.next U s i ∈ T :=
    hsub _ (CanonicalSupportWalk.next_mem U s i hbranchU)
  have hstrict : IsStrictPrefix s (CanonicalSupportWalk.next U s i) :=
    ((SkewBranchGeometry.immediateSuccB_iff U s _).1 hnextU.1).2.1
  obtain ⟨t, _ht, hstep, hst, hprefix⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path
      T s (CanonicalSupportWalk.next U s i) hnextTmem hstrict
  have hlen : (s ++ [i]).length ≤ t.length := by
    have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hst
    simp only [List.length_append, List.length_singleton]
    omega
  have hdir : IsPrefix (s ++ [i]) t :=
    CutFrontier.prefix_of_prefix_length_le hnextU.2 hprefix hlen
  have hbranchT : SkewTree.uniqueBranchB T s i = true :=
    unique_direction_of_immediate T hT hnonT s t
      (hsub s hs) hstep i
  have hnext : CanonicalSupportWalk.next T s i = t :=
    SupportReachability.next_eq_of_immediate T s t i
      hbranchT hstep hdir
  simpa only [hnext] using hprefix

/-- At a retained early parent, a genuine new directional successor
extends the original successor. The stated height budget uses the
original intrinsic rank; address transport proves that it is also the
new rank, so the new branch is constructed from completeness. -/
theorem successor_prefix_of_retained_parent
    {b k q : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonT : T.length ≠ 1) (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U)
    (s : Node b) (hs : s ∈ T) (hbefore : ForwardAux s cut)
    (hbudget : SkewTree.heightAt T s + 1 < q) (i : Fin b) :
    IsPrefix (CanonicalSupportWalk.next T s i)
      (CanonicalSupportWalk.next U s i) := by
  have hsU : s ∈ U := hkeep s hs hbefore
  have haddress :=
    ForwardCompleteInitialTransport.inverseAddress_eq_of_retained_cut
      T U hT hU hnonT hnonU hsub cut hkeep s hs hbefore
  have hrank : SkewTree.heightAt U s = SkewTree.heightAt T s := by
    calc
      SkewTree.heightAt U s =
          (inverseAddress U hU hnonU ⟨s, hsU⟩).1.length :=
        (inverse_length U hU hnonU ⟨s, hsU⟩).symm
      _ = (inverseAddress T hT hnonT ⟨s, hs⟩).1.length :=
        congrArg List.length haddress
      _ = SkewTree.heightAt T s := inverse_length T hT hnonT ⟨s, hs⟩
  have hlevel : SkewTree.heightAt U s + 1 < q := by
    simpa only [hrank] using hbudget
  have hbranchU : SkewTree.uniqueBranchB U s i = true :=
    branch_of_height_lt U hU hnonU s hsU hlevel i
  exact successor_prefix_of_subset T U hT hnonT hsub s hsU i hbranchU

/-- Extending a node outside the strict forward cut keeps it outside
and preserves its first ambient boundary. The new outside-cut proof is
derived from prefix closure of the initial segment. -/
theorem firstBoundary_eq_of_prefix
    {b : Nat} (cut s t : Node b)
    (hs : ¬ BeforeCut cut s) (hprefix : IsPrefix s t) :
    ∃ ht : ¬ BeforeCut cut t,
      firstBoundary cut t ht = firstBoundary cut s hs := by
  have ht : ¬ BeforeCut cut t := by
    intro hbefore
    exact hs (ForwardSignatureInteriorPersistence.beforeCut_of_prefix
      hprefix hbefore)
  refine ⟨ht, ?_⟩
  have hboundary : Boundary cut t (firstBoundary cut s hs) :=
    ⟨isPrefix_trans (firstBoundary_spec cut s hs).1 hprefix,
      (firstBoundary_spec cut s hs).2⟩
  exact ((Classical.choose_spec
    (existsUnique_boundary_on_path cut t ht)).2
      (firstBoundary cut s hs) hboundary).symm

/-- The first boundary of an outgoing support edge at an early retained
parent is unchanged by complete refinement. The boundary cut is separate
from the retention cut, allowing this statement to serve an earlier
signature during an increasing-cut fusion. -/
theorem firstBoundary_transport_of_retained_parent
    {b k q : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonT : T.length ≠ 1) (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U)
    (s : Node b) (hs : s ∈ T) (hbefore : ForwardAux s cut)
    (hbudget : SkewTree.heightAt T s + 1 < q) (i : Fin b)
    (boundaryCut : Node b)
    (hout : ¬ BeforeCut boundaryCut (CanonicalSupportWalk.next T s i)) :
    ∃ houtU : ¬ BeforeCut boundaryCut (CanonicalSupportWalk.next U s i),
      firstBoundary boundaryCut (CanonicalSupportWalk.next U s i) houtU =
        firstBoundary boundaryCut (CanonicalSupportWalk.next T s i) hout :=
  firstBoundary_eq_of_prefix boundaryCut _ _ hout
    (successor_prefix_of_retained_parent T U hT hU hnonT hnonU
      hsub cut hkeep s hs hbefore hbudget i)

/-- Necessary-premise regression: both unary supports are genuinely
complete and the whole initial cut is retained, but the retained parent
is terminal in U. Its totalized U successor stays at the parent, so the
successor-prefix conclusion fails without the new-height budget. This
does not contradict the preceding theorem, whose budget is false here. -/
theorem terminal_parent_counterexample :
    let T : List (Node 1) := [[], [0], [0, 0]]
    let U : List (Node 1) := [[], [0]]
    let s : Node 1 := [0]
    SkewTree.completeB SkewTree.forwardAuxB 3 T = true ∧
    SkewTree.completeB SkewTree.forwardAuxB 2 U = true ∧
    T.length ≠ 1 ∧ U.length ≠ 1 ∧
    (∀ t, t ∈ U → t ∈ T) ∧
    (∀ t, t ∈ T → ForwardAux t s → t ∈ U) ∧
    s ∈ T ∧ ForwardAux s s ∧
    ¬ (SkewTree.heightAt T s + 1 < 2) ∧
    ¬ IsPrefix (CanonicalSupportWalk.next T s 0)
        (CanonicalSupportWalk.next U s 0) := by
  dsimp only
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_,
    by simp, CanonicalForwardAuxIso.forwardAux_refl _, by decide, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro t ht hbefore
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · simp
    · simp
    · simp [ForwardAux] at hbefore
  · have hnextT : CanonicalSupportWalk.next
        ([[], [0], [0, 0]] : List (Node 1)) [0] 0 = [0, 0] :=
      SupportReachability.next_eq_of_immediate _ _ _ _
        (by decide) (by decide) ⟨[], by simp⟩
    have hempty : SkewTree.branchWitnesses
        ([[], [0]] : List (Node 1)) [0] 0 = [] := by decide
    have hnextU : CanonicalSupportWalk.next
        ([[], [0]] : List (Node 1)) [0] 0 = [0] := by
      simp only [CanonicalSupportWalk.next, hempty]
    rw [hnextT, hnextU]
    intro hprefix
    have hlength := prefix_length_le hprefix
    simp at hlength

end DualTree.ForwardCompleteBoundaryTransport
