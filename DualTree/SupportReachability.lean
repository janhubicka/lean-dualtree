import DualTree.CanonicalSupportInjective
import DualTree.CompleteInteriorBranching

/-!
# Every support vertex has an address in the canonical walk

Rather than assuming surjectivity of the abstract canonical map I_T,
construct an address for each node of a complete skew support.

From a support vertex s and a proper support descendant t, choose
the first immediate support successor u on their common branch.
The successor u has a definite ambient direction i; completeness
makes the corresponding directional successor unique. Recursing from
u to t strictly decreases the ambient length gap.

This constructs an admissible (not yet explicitly k-bounded) address.
Its length is exactly the intrinsic rank of the target node. A separate
bound heightAt T t < k will therefore complete surjectivity of the
previously constructed embedding b^{<k} → T.
-/

namespace DualTree.SupportReachability

/-- A list containing two distinct vertices is not a singleton. -/
theorem nonsingleton_of_distinct_members {b : Nat}
    (T : List (Node b))
    {s t : Node b} (hs : s ∈ T) (ht : t ∈ T) (hne : s ≠ t) :
    T.length ≠ 1 := by
  intro hone
  cases T with
  | nil =>
      simp at hs
  | cons a tail =>
      cases tail with
      | nil =>
          have hsa : s = a := by simpa using hs
          have hta : t = a := by simpa using ht
          exact hne (hsa.trans hta.symm)
      | cons a' rest =>
          simp at hone

/-- Every strict ambient extension begins in a definite direction. -/
theorem first_direction_of_strictPrefix {b : Nat}
    {s t : Node b} (hst : IsStrictPrefix s t) :
    ∃ i : Fin b, IsPrefix (s ++ [i]) t := by
  rcases hst with ⟨⟨tail, htail⟩, hne⟩
  cases tail with
  | nil =>
      have heq : t = s := by simpa using htail
      exact (hne heq.symm).elim
  | cons i rest =>
      refine ⟨i, rest, ?_⟩
      calc
        t = s ++ (i :: rest) := htail
        _ = (s ++ [i]) ++ rest := by simp [List.append_assoc]

/-- A support vertex with an actual immediate successor is non-leaf,
so completeness yields every directional successor uniquely. -/
theorem unique_direction_of_immediate {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (s u : Node b) (hs : s ∈ T)
    (hstep : SkewTree.immediateSuccB T s u = true)
    (i : Fin b) :
    SkewTree.uniqueBranchB T s i = true := by
  rcases (SkewBranchGeometry.immediateSuccB_iff T s u).1 hstep with
    ⟨huT, hsu, _⟩
  have hnon : T.length ≠ 1 :=
    nonsingleton_of_distinct_members T hs huT hsu.2
  have huSucc : u ∈ SkewTree.immediateSuccs T s := by
    change u ∈ T.filter (fun t => SkewTree.immediateSuccB T s t)
    exact List.mem_filter.mpr ⟨huT, hstep⟩
  have hnonleaf : (SkewTree.immediateSuccs T s).length ≠ 0 := by
    intro hzero
    have hnil : SkewTree.immediateSuccs T s = [] := by
      cases hlist : SkewTree.immediateSuccs T s with
      | nil => rfl
      | cons v vs => simp [hlist] at hzero
    simp [hnil] at huSucc
  exact CompleteInteriorBranching.fullDirections_of_complete_nonleaf_total
    SkewTree.paperAuxB T hcomplete hnon
    (fun a c _ => SkewMeetInstantiation.paperAuxB_total a c)
    s hs hnonleaf i

/-- A unique directional successor agrees with a specified immediate
successor which lies in that direction. -/
theorem next_eq_of_immediate {b : Nat}
    (T : List (Node b)) (s u : Node b) (i : Fin b)
    (hunique : SkewTree.uniqueBranchB T s i = true)
    (hstep : SkewTree.immediateSuccB T s u = true)
    (hdir : IsPrefix (s ++ [i]) u) :
    CanonicalSupportWalk.next T s i = u := by
  have hnext := CanonicalSupportWalk.next_unique T s i hunique
  have hnextMem :
      CanonicalSupportWalk.next T s i ∈
        SkewTree.branchWitnesses T s i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      T s (CanonicalSupportWalk.next T s i) i).2 hnext
  have huMem : u ∈ SkewTree.branchWitnesses T s i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff T s u i).2
      ⟨hstep, hdir⟩
  exact SkewBranchGeometry.eq_of_mem_uniqueBranch
    T s i hunique hnextMem huMem

/-- Every support descendant can be reached through a finite sequence
of uniquely determined directional immediate successors. -/
theorem walk_address_of_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (s t : Node b)
    (hs : s ∈ T) (ht : t ∈ T) (hst : IsPrefix s t) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible T s address ∧
      CanonicalSupportWalk.walk T s address = t := by
  have hmain : ∀ d : Nat, ∀ s t : Node b,
      s ∈ T → t ∈ T → IsPrefix s t →
      t.length - s.length = d →
      ∃ address : Node b,
        CanonicalSupportWalk.Admissible T s address ∧
        CanonicalSupportWalk.walk T s address = t := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro s t hs ht hst hgap
        by_cases heq : s = t
        · subst t
          exact ⟨[], trivial, rfl⟩
        · have hstrict : IsStrictPrefix s t := ⟨hst, heq⟩
          obtain ⟨u, huT, hstep, hsu, hut⟩ :=
            SkewBranchGeometry.exists_first_immediate_on_path
              T s t ht hstrict
          obtain ⟨i, hdir⟩ := first_direction_of_strictPrefix hsu
          have hbranch : SkewTree.uniqueBranchB T s i = true :=
            unique_direction_of_immediate T hcomplete s u hs hstep i
          have hnext : CanonicalSupportWalk.next T s i = u :=
            next_eq_of_immediate T s u i hbranch hstep hdir
          have hsmaller : t.length - u.length < d := by
            have hsulen :=
              MeetClosedFromBranching.length_lt_of_strictPrefix hsu
            have hutlen := prefix_length_le hut
            omega
          obtain ⟨tail, hvalid, hwalk⟩ :=
            ih (t.length - u.length) hsmaller
              u t huT ht hut rfl
          refine ⟨i :: tail, ?_, ?_⟩
          · change SkewTree.uniqueBranchB T s i = true ∧
              CanonicalSupportWalk.Admissible T
                (CanonicalSupportWalk.next T s i) tail
            refine ⟨hbranch, ?_⟩
            rwa [hnext]
          · change
              CanonicalSupportWalk.walk T
                (CanonicalSupportWalk.next T s i) tail = t
            simpa [hnext] using hwalk
  exact hmain (t.length - s.length) s t hs ht hst rfl

/-- Each admissible traversal from a support vertex advances its
intrinsic height by the number of source directions. -/
theorem walk_height_of_admissible {b : Nat}
    (T : List (Node b)) (hnd : T.Nodup) :
    ∀ (address s : Node b),
      s ∈ T →
      CanonicalSupportWalk.Admissible T s address →
      SkewTree.heightAt T (CanonicalSupportWalk.walk T s address) =
        SkewTree.heightAt T s + address.length := by
  intro address
  induction address with
  | nil =>
      intro s hs hadm
      rfl
  | cons i tail ih =>
      intro s hs hvalid
      rcases hvalid with ⟨hbranch, htail_valid⟩
      have hnextMem : CanonicalSupportWalk.next T s i ∈ T :=
        CanonicalSupportWalk.next_mem T s i hbranch
      have hnextRank :
          SkewTree.heightAt T (CanonicalSupportWalk.next T s i) =
            SkewTree.heightAt T s + 1 :=
        ImmediateSupportHeight.heightAt_next T s i hnd hs hbranch
      have htailRank :=
        ih (CanonicalSupportWalk.next T s i) hnextMem htail_valid
      change
        SkewTree.heightAt T
          (CanonicalSupportWalk.walk T
            (CanonicalSupportWalk.next T s i) tail) =
        SkewTree.heightAt T s + (i :: tail).length
      rw [htailRank, hnextRank]
      simp only [List.length_cons]
      omega

/-- Every support vertex has an admissible source address of length
equal to its intrinsic height. The remaining issue is bounding that
height by k, so that the address belongs to the source b^{<k}. -/
theorem support_has_address {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : Node b) (ht : t ∈ T) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible T
        (CompleteSupportRoot.rootOf T hcomplete) address ∧
      CompleteSupportRoot.canonicalWalk T hcomplete address = t ∧
      address.length = SkewTree.heightAt T t := by
  let root := CompleteSupportRoot.rootOf T hcomplete
  have hrootMem : root ∈ T := CompleteSupportRoot.rootOf_mem T hcomplete
  have hrootPrefix : IsPrefix root t :=
    CompleteSupportRoot.rootOf_prefix T hcomplete t ht
  obtain ⟨address, hvalid, hwalk⟩ :=
    walk_address_of_prefix T hcomplete root t hrootMem ht hrootPrefix
  have hrootRank : SkewTree.heightAt T root = 0 :=
    ImmediateSupportHeight.heightAt_root_zero T root
      (CompleteSupportRoot.rootOf_prefix T hcomplete)
  have hrank :=
    walk_height_of_admissible T
      (CompleteSupportAddresses.support_nodup T hcomplete)
      address root hrootMem hvalid
  have hlength : address.length = SkewTree.heightAt T t := by
    rw [hwalk, hrootRank] at hrank
    omega
  refine ⟨address, hvalid, ?_, hlength⟩
  simpa [CompleteSupportRoot.canonicalWalk, root] using hwalk

end DualTree.SupportReachability
