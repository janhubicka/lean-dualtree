import DualTree.CompleteSkewMeet

/-!
# Meet closure forces unique immediate successors in every direction

The established finite-tree API proves that a rooted support with
at most one immediate successor per ambient direction is meet-closed.
We prove the converse, which does not require rootedness.

If two different immediate successors x,y of a node s lie in the
same direction i, their ambient meet m extends s⌢i. Under meet
closure this meet belongs to the support; since x ≠ y, it lies
strictly between s and at least one of x,y, contradicting the
definition of immediate support successor.

For a rooted support this gives an equivalence between ambient meet
closure and directional uniqueness. It will be useful when checking
semi-complete branching of the reconstructed Lemma 27 tree.
-/

namespace DualTree.MeetClosedDirectionConverse

/-- Meet closure excludes multiple immediate support successors
in the same ambient direction, even in an unrooted support. -/
theorem atMostOneDirection_of_meetClosed {b : Nat}
    (S : List (Node b)) (hmeet : MeetGeometry.MeetClosed S) :
    MeetClosedFromBranching.AtMostOneDirection S := by
  intro s hs i x y hx hy
  rcases (SkewBranchGeometry.mem_branchWitnesses_iff S s x i).1 hx with
    ⟨hxImm, hix⟩
  rcases (SkewBranchGeometry.mem_branchWitnesses_iff S s y i).1 hy with
    ⟨hyImm, hiy⟩
  have hxMem : x ∈ S :=
    ((SkewBranchGeometry.immediateSuccB_iff S s x).1 hxImm).1
  have hyMem : y ∈ S :=
    ((SkewBranchGeometry.immediateSuccB_iff S s y).1 hyImm).1
  let m := MeetGeometry.commonPrefix x y
  have hm : m ∈ S := hmeet x y hxMem hyMem
  have hdirM : IsPrefix (s ++ [i]) m :=
    MeetGeometry.prefix_commonPrefix hix hiy
  have hsM : IsPrefix s m :=
    isPrefix_trans ⟨[i], rfl⟩ hdirM
  have hlen : s.length < m.length := by
    have hle := prefix_length_le hdirM
    simp only [List.length_append, List.length_singleton] at hle
    omega
  have hstrict : IsStrictPrefix s m := by
    refine ⟨hsM, ?_⟩
    intro heq
    have heqLen := congrArg List.length heq
    omega
  by_cases hmx : m = x
  · by_cases hmy : m = y
    · exact hmx.symm.trans hmy
    · have hmyStrict : IsStrictPrefix m y :=
        ⟨MeetGeometry.commonPrefix_prefix_right x y, hmy⟩
      exact False.elim
        (((SkewBranchGeometry.immediateSuccB_iff S s y).1
          hyImm).2.2 m hm ⟨hstrict, hmyStrict⟩)
  · have hmxStrict : IsStrictPrefix m x :=
      ⟨MeetGeometry.commonPrefix_prefix_left x y, hmx⟩
    exact False.elim
      (((SkewBranchGeometry.immediateSuccB_iff S s x).1
        hxImm).2.2 m hm ⟨hstrict, hmxStrict⟩)

/-- In a rooted finite support, the geometric meet-closure and
branch-direction uniqueness conditions are equivalent. -/
theorem meetClosed_iff_atMostOneDirection_of_rooted {b : Nat}
    (S : List (Node b)) (hroot : SkewTree.rootedB S = true) :
    MeetGeometry.MeetClosed S ↔
      MeetClosedFromBranching.AtMostOneDirection S :=
  ⟨atMostOneDirection_of_meetClosed S,
    MeetClosedFromBranching.meetClosed_of_rooted_uniqueDirections S hroot⟩

end DualTree.MeetClosedDirectionConverse
