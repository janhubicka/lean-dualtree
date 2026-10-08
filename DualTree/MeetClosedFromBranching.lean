import DualTree.SkewBranchGeometry

/-!
# Ambient meet closure from uniqueness of directional support successors

This is the finite combinatorial reduction behind the Lemma 27 support
geometry.  A rooted finite set of tree nodes is closed under ambient meets
as soon as every support node has at most one immediate support successor
in each ambient direction.

The proof raises a common support prefix by one immediate successor at a
time. The remaining source-facing task is to extract global directional
uniqueness from clause (iv) of the complete-skew definition.
-/

namespace DualTree.MeetClosedFromBranching

/-- At every support node, each ambient direction selects at most one immediate successor. -/
def AtMostOneDirection {b : Nat} (T : List (Node b)) : Prop :=
  ∀ (s : Node b), s ∈ T → ∀ (i : Fin b) (x y : Node b),
    x ∈ SkewTree.branchWitnesses T s i →
    y ∈ SkewTree.branchWitnesses T s i → x = y

/-- A strict prefix has strictly smaller ambient word length. -/
theorem length_lt_of_strictPrefix {b : Nat}
    {s t : Node b} (h : IsStrictPrefix s t) :
    s.length < t.length := by
  have hle : s.length ≤ t.length := prefix_length_le h.1
  by_contra hn
  have hlen : s.length = t.length := by omega
  exact h.2 (CutPreservation.prefix_eq_of_length_eq h.1 hlen)

/--
When a support node is strictly below the ambient meet of two support
nodes, uniqueness of the branching directions gives a strictly longer
common support prefix.
-/
theorem exists_longer_common_support_prefix {b : Nat}
    (T : List (Node b)) (hunique : AtMostOneDirection T)
    (x y z : Node b)
    (hx : x ∈ T) (hy : y ∈ T)
    (hz : z ∈ T)
    (hzm : IsStrictPrefix z (MeetGeometry.commonPrefix x y)) :
    ∃ u, u ∈ T ∧ IsStrictPrefix z u ∧
      IsPrefix u (MeetGeometry.commonPrefix x y) := by
  let m := MeetGeometry.commonPrefix x y
  have hzx : IsStrictPrefix z x := by
    refine ⟨isPrefix_trans hzm.1
      (MeetGeometry.commonPrefix_prefix_left x y), ?_⟩
    intro heq
    have hmx : IsPrefix m x :=
      MeetGeometry.commonPrefix_prefix_left x y
    rw [← heq] at hmx
    exact hzm.2 (isPrefix_antisymm hzm.1 hmx)
  have hzy : IsStrictPrefix z y := by
    refine ⟨isPrefix_trans hzm.1
      (MeetGeometry.commonPrefix_prefix_right x y), ?_⟩
    intro heq
    have hmy : IsPrefix m y :=
      MeetGeometry.commonPrefix_prefix_right x y
    rw [← heq] at hmy
    exact hzm.2 (isPrefix_antisymm hzm.1 hmy)
  obtain ⟨u, huT, huB, hzu, hux⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path T z x hx hzx
  obtain ⟨v, hvT, hvB, hzv, hvy⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path T z y hy hzy
  rcases hzm.1 with ⟨tail, htail⟩
  cases tail with
  | nil =>
      have heq : z = m := by simpa using htail.symm
      exact (hzm.2 heq).elim
  | cons i rest =>
      have hdir : IsPrefix (z ++ [i]) m := by
        refine ⟨rest, ?_⟩
        calc
          m = z ++ (i :: rest) := htail
          _ = (z ++ [i]) ++ rest := by simp [List.append_assoc]
      have hdirX : IsPrefix (z ++ [i]) x :=
        isPrefix_trans hdir (MeetGeometry.commonPrefix_prefix_left x y)
      have hdirY : IsPrefix (z ++ [i]) y :=
        isPrefix_trans hdir (MeetGeometry.commonPrefix_prefix_right x y)
      have hlenU : (z ++ [i]).length ≤ u.length := by
        have hzulen := length_lt_of_strictPrefix hzu
        simp only [List.length_append, List.length_singleton]
        omega
      have hlenV : (z ++ [i]).length ≤ v.length := by
        have hzvlen := length_lt_of_strictPrefix hzv
        simp only [List.length_append, List.length_singleton]
        omega
      have hdirU : IsPrefix (z ++ [i]) u :=
        CutFrontier.prefix_of_prefix_length_le hdirX hux hlenU
      have hdirV : IsPrefix (z ++ [i]) v :=
        CutFrontier.prefix_of_prefix_length_le hdirY hvy hlenV
      have huMem : u ∈ SkewTree.branchWitnesses T z i :=
        (SkewBranchGeometry.mem_branchWitnesses_iff T z u i).2
          ⟨huB, hdirU⟩
      have hvMem : v ∈ SkewTree.branchWitnesses T z i :=
        (SkewBranchGeometry.mem_branchWitnesses_iff T z v i).2
          ⟨hvB, hdirV⟩
      have huv : u = v := hunique z hz i u v huMem hvMem
      have huy : IsPrefix u y := by simpa [huv] using hvy
      exact ⟨u, huT, hzu,
        MeetGeometry.prefix_commonPrefix hux huy⟩

/-- The common ambient prefix of two support points is in T if it has some support prefix. -/
theorem commonPrefix_mem_of_support_root {b : Nat}
    (T : List (Node b)) (hunique : AtMostOneDirection T)
    (x y root : Node b)
    (hx : x ∈ T) (hy : y ∈ T) (hr : root ∈ T)
    (hroot : IsPrefix root (MeetGeometry.commonPrefix x y)) :
    MeetGeometry.commonPrefix x y ∈ T := by
  let m := MeetGeometry.commonPrefix x y
  have ascend :
      ∀ d : Nat, ∀ z : Node b, z ∈ T → IsPrefix z m →
        m.length - z.length = d → m ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro z hz hzm hgap
        by_cases hEq : z = m
        · simpa [hEq] using hz
        · obtain ⟨u, huT, hzu, hum⟩ :=
            exists_longer_common_support_prefix T hunique x y z
              hx hy hz ⟨hzm, hEq⟩
          have hlenZ : z.length < u.length :=
            length_lt_of_strictPrefix hzu
          have hlenU : u.length ≤ m.length := prefix_length_le hum
          have hsmaller : m.length - u.length < d := by omega
          exact ih (m.length - u.length) hsmaller u huT hum rfl
  exact ascend (m.length - root.length) root hr hroot rfl

/-- Rooted support with unique immediate successor in each direction is meet-closed. -/
theorem meetClosed_of_rooted_uniqueDirections {b : Nat}
    (T : List (Node b))
    (hrooted : SkewTree.rootedB T = true)
    (hunique : AtMostOneDirection T) :
    MeetGeometry.MeetClosed T := by
  intro x y hx hy
  rcases List.any_eq_true.mp hrooted with
    ⟨root, hr, hall⟩
  have hrootX : IsPrefix root x :=
    DirectionalSupport.prefix_of_isPrefixOf_true
      ((List.all_eq_true.mp hall) x hx)
  have hrootY : IsPrefix root y :=
    DirectionalSupport.prefix_of_isPrefixOf_true
      ((List.all_eq_true.mp hall) y hy)
  exact commonPrefix_mem_of_support_root T hunique x y root
    hx hy hr (MeetGeometry.prefix_commonPrefix hrootX hrootY)

end DualTree.MeetClosedFromBranching
