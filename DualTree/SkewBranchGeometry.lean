import DualTree.SkewLevelOrder

/-!
# First successors on support paths and uniqueness of branching directions

A skew support is not necessarily ambient-prefix closed.  Its immediate
successors are nonetheless defined with respect to the finite support.
This file bridges the Boolean implementation of that notion with ordinary
strict prefixes and shows that a path to any proper support descendant
has an immediate support successor.

The local branch-uniqueness theorem is the first ingredient for proving
that complete skew supports are ambient meet-closed.  It does not yet
deduce uniform branch uniqueness from the skew axioms.
-/

namespace DualTree.SkewBranchGeometry

/-- Translate the paper's prefix witness into the Boolean list test. -/
theorem isPrefixOf_true_of_prefix {b : Nat}
    {s t : Node b} (hst : IsPrefix s t) :
    s.isPrefixOf t = true := by
  rcases hst with ⟨u, rfl⟩
  induction s with
  | nil => simp
  | cons a as ih =>
      simp [List.isPrefixOf_cons_cons, ih]

/-- The executable proper-prefix predicate has the intended meaning. -/
theorem strictPrefixB_iff {b : Nat} (s t : Node b) :
    SkewTree.strictPrefixB s t = true ↔ IsStrictPrefix s t := by
  constructor
  · intro h
    simp only [SkewTree.strictPrefixB, Bool.and_eq_true] at h
    refine ⟨DirectionalSupport.prefix_of_isPrefixOf_true h.1, ?_⟩
    intro heq
    subst t
    simp at h
  · rintro ⟨hp, hne⟩
    simp [SkewTree.strictPrefixB, isPrefixOf_true_of_prefix hp, hne]

/-- An immediate support successor is a proper extension with no intervening support node. -/
theorem immediateSuccB_iff {b : Nat}
    (T : List (Node b)) (s t : Node b) :
    SkewTree.immediateSuccB T s t = true ↔
      t ∈ T ∧ IsStrictPrefix s t ∧
        ∀ u, u ∈ T →
          ¬ (IsStrictPrefix s u ∧ IsStrictPrefix u t) := by
  constructor
  · intro h
    simp only [SkewTree.immediateSuccB, Bool.and_eq_true] at h
    rcases h with ⟨⟨ht, hp⟩, hnone⟩
    refine ⟨(by simpa using ht), (strictPrefixB_iff s t).1 hp, ?_⟩
    intro u hu ⟨hsu, hut⟩
    have hhit : T.any (fun v =>
        SkewTree.strictPrefixB s v &&
          SkewTree.strictPrefixB v t) = true :=
      List.any_eq_true.mpr ⟨u, hu, by
        simp [(strictPrefixB_iff s u).2 hsu,
          (strictPrefixB_iff u t).2 hut]⟩
    simp [hhit] at hnone
  · rintro ⟨ht, hp, hno⟩
    have hnone : T.any (fun v =>
        SkewTree.strictPrefixB s v &&
          SkewTree.strictPrefixB v t) = false := by
      cases htest : T.any (fun v =>
          SkewTree.strictPrefixB s v &&
            SkewTree.strictPrefixB v t) with
      | false => rfl
      | true =>
          rcases List.any_eq_true.mp htest with ⟨u, hu, htestu⟩
          simp only [Bool.and_eq_true] at htestu
          rcases htestu with ⟨hsu, hut⟩
          exact (hno u hu
            ⟨(strictPrefixB_iff s u).1 hsu,
             (strictPrefixB_iff u t).1 hut⟩).elim
    simp [SkewTree.immediateSuccB, ht,
      (strictPrefixB_iff s t).2 hp, hnone]

/-- Membership in a directional successor list is the expected conjunction. -/
theorem mem_branchWitnesses_iff {b : Nat}
    (T : List (Node b)) (s t : Node b) (i : Fin b) :
    t ∈ SkewTree.branchWitnesses T s i ↔
      SkewTree.immediateSuccB T s t = true ∧
        IsPrefix (s ++ [i]) t := by
  constructor
  · intro ht
    change t ∈ T.filter
      (fun v => SkewTree.immediateSuccB T s v &&
        (s ++ [i]).isPrefixOf v) at ht
    rcases List.mem_filter.mp ht with ⟨_ht, htest⟩
    simp only [Bool.and_eq_true] at htest
    rcases htest with ⟨hs, hp⟩
    exact ⟨hs, DirectionalSupport.prefix_of_isPrefixOf_true hp⟩
  · rintro ⟨hs, hp⟩
    change t ∈ T.filter
      (fun v => SkewTree.immediateSuccB T s v &&
        (s ++ [i]).isPrefixOf v)
    have ht : t ∈ T := ((immediateSuccB_iff T s t).1 hs).1
    exact List.mem_filter.mpr ⟨ht, by
      simp [hs, isPrefixOf_true_of_prefix hp]⟩

/--
Every proper extension of a node by a member of the support passes
through an immediate support successor.  The support need not contain
all ambient prefixes or even contain the starting node.
-/
theorem exists_first_immediate_on_path {b : Nat}
    (T : List (Node b)) (root t : Node b)
    (ht : t ∈ T) (hroot : IsStrictPrefix root t) :
    ∃ u, u ∈ T ∧
      SkewTree.immediateSuccB T root u = true ∧
      IsStrictPrefix root u ∧ IsPrefix u t := by
  let I : Node b → Prop := fun z => ¬ IsStrictPrefix root z
  have hout : ¬ I t := fun h => h hroot
  obtain ⟨u, hu, hut⟩ :=
    CutFrontier.exists_frontier_above T I ht hout
  have hru : IsStrictPrefix root u := by
    by_contra hn
    exact hu.2.1 hn
  have hno : ∀ v, v ∈ T →
      ¬ (IsStrictPrefix root v ∧ IsStrictPrefix v u) := by
    intro v hv ⟨hrv, hvu⟩
    exact (hu.2.2 v hv hvu) hrv
  exact ⟨u, hu.1,
    (immediateSuccB_iff T root u).2 ⟨hu.1, hru, hno⟩,
    hru, hut⟩

/-- A Boolean unique-branch witness cannot contain two different successors. -/
theorem eq_of_mem_uniqueBranch {b : Nat}
    (T : List (Node b)) (s : Node b) (i : Fin b)
    (hunique : SkewTree.uniqueBranchB T s i = true)
    {x y : Node b}
    (hx : x ∈ SkewTree.branchWitnesses T s i)
    (hy : y ∈ SkewTree.branchWitnesses T s i) :
    x = y := by
  have hlen : (SkewTree.branchWitnesses T s i).length = 1 := by
    simpa [SkewTree.uniqueBranchB] using hunique
  cases heq : SkewTree.branchWitnesses T s i with
  | nil =>
      simp [heq] at hlen
  | cons z rest =>
      cases rest with
      | nil =>
          have hxz : x = z := by simpa [heq] using hx
          have hyz : y = z := by simpa [heq] using hy
          exact hxz.trans hyz.symm
      | cons u us =>
          simp [heq] at hlen

end DualTree.SkewBranchGeometry
