import DualTree.CompleteSupportRoot
import DualTree.SupportHeightRanks

/-!
# Exact intrinsic-height change at immediate support successors

For an immediate support successor t of s, the proper T-predecessors
of t are exactly the proper T-predecessors of s, together with s.
The proof uses no skewness, only duplicate-free finite support and
the absence of support points strictly between s and t.

The resulting rank identity is the numerical input needed to establish
admissibility of every bounded source address in a complete skew tree.
-/

namespace DualTree.ImmediateSupportHeight

/-- The executable predecessor list has its intended logical membership test. -/
theorem mem_preds_iff {b : Nat}
    (T : List (Node b)) (t u : Node b) :
    u ∈ SkewTree.preds T t ↔ u ∈ T ∧ IsStrictPrefix u t := by
  change u ∈ T.filter (fun x => SkewTree.strictPrefixB x t) ↔
    u ∈ T ∧ IsStrictPrefix u t
  rw [List.mem_filter]
  exact and_congr_right (fun _ =>
    SkewBranchGeometry.strictPrefixB_iff u t)

/-- The predecessor set of an immediate successor gains precisely its parent. -/
theorem mem_preds_immediate_iff {b : Nat}
    (T : List (Node b)) (s t u : Node b)
    (hs : s ∈ T)
    (hstep : SkewTree.immediateSuccB T s t = true) :
    u ∈ SkewTree.preds T t ↔
      u ∈ SkewTree.preds T s ∨ u = s := by
  rcases (SkewBranchGeometry.immediateSuccB_iff T s t).1 hstep with
    ⟨_ht, hst, hno⟩
  constructor
  · intro hu
    rcases (mem_preds_iff T t u).1 hu with ⟨huT, hut⟩
    rcases le_total u.length s.length with hlen | hlen
    · have hus : IsPrefix u s :=
        CutFrontier.prefix_of_prefix_length_le hut.1 hst.1 hlen
      by_cases heq : u = s
      · exact Or.inr heq
      · exact Or.inl ((mem_preds_iff T s u).2 ⟨huT, hus, heq⟩)
    · have hsu : IsPrefix s u :=
        CutFrontier.prefix_of_prefix_length_le hst.1 hut.1 hlen
      by_cases heq : u = s
      · exact Or.inr heq
      · have hsu' : IsStrictPrefix s u := ⟨hsu, Ne.symm heq⟩
        exact (hno u huT ⟨hsu', hut⟩).elim
  · intro hu
    rcases hu with hu | heq
    · rcases (mem_preds_iff T s u).1 hu with ⟨huT, hus⟩
      have hut : IsStrictPrefix u t := by
        refine ⟨isPrefix_trans hus.1 hst.1, ?_⟩
        intro heq
        have hlenus := MeetClosedFromBranching.length_lt_of_strictPrefix hus
        have hlenst := MeetClosedFromBranching.length_lt_of_strictPrefix hst
        rw [← heq] at hlenst
        omega
      exact (mem_preds_iff T t u).2 ⟨huT, hut⟩
    · subst u
      exact (mem_preds_iff T t s).2 ⟨hs, hst⟩

/-- Every immediate support successor increases intrinsic height by exactly one. -/
theorem heightAt_immediate {b : Nat}
    (T : List (Node b)) (s t : Node b)
    (hnd : T.Nodup) (hs : s ∈ T)
    (hstep : SkewTree.immediateSuccB T s t = true) :
    SkewTree.heightAt T t = SkewTree.heightAt T s + 1 := by
  classical
  have hset :
      (SkewTree.preds T t).toFinset =
        insert s (SkewTree.preds T s).toFinset := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_insert]
    rw [mem_preds_immediate_iff T s t u hs hstep]
    exact or_comm
  have hnot : s ∉ (SkewTree.preds T s).toFinset := by
    intro hmem
    have hss := (mem_preds_iff T s s).1
      (List.mem_toFinset.mp hmem)
    exact hss.2.2 rfl
  have hndt : (SkewTree.preds T t).Nodup := by
    unfold SkewTree.preds
    exact hnd.filter _
  have hnds : (SkewTree.preds T s).Nodup := by
    unfold SkewTree.preds
    exact hnd.filter _
  change (SkewTree.preds T t).length =
    (SkewTree.preds T s).length + 1
  calc
    (SkewTree.preds T t).length =
        (SkewTree.preds T t).toFinset.card :=
      (List.toFinset_card_of_nodup hndt).symm
    _ = (insert s (SkewTree.preds T s).toFinset).card :=
      congrArg Finset.card hset
    _ = (SkewTree.preds T s).toFinset.card + 1 := by
      simp [hnot]
    _ = (SkewTree.preds T s).length + 1 := by
      rw [List.toFinset_card_of_nodup hnds]

/-- Every support root has intrinsic height zero. -/
theorem heightAt_root_zero {b : Nat}
    (T : List (Node b)) (root : Node b)
    (hroot : ∀ t, t ∈ T → IsPrefix root t) :
    SkewTree.heightAt T root = 0 := by
  cases hpred : SkewTree.preds T root with
  | nil =>
      simp [SkewTree.heightAt, hpred]
  | cons u us =>
      have hu : u ∈ SkewTree.preds T root := by
        simp [hpred]
      rcases (mem_preds_iff T root u).1 hu with ⟨huT, hur⟩
      have hru : IsPrefix root u := hroot u huT
      have heq : u = root := isPrefix_antisymm hur.1 hru
      exact (hur.2 heq).elim

/-- The constructive transition increases intrinsic height at any unique branch. -/
theorem heightAt_next {b : Nat}
    (T : List (Node b)) (s : Node b) (i : Fin b)
    (hnd : T.Nodup) (hs : s ∈ T)
    (hunique : SkewTree.uniqueBranchB T s i = true) :
    SkewTree.heightAt T (CanonicalSupportWalk.next T s i) =
      SkewTree.heightAt T s + 1 :=
  heightAt_immediate T s (CanonicalSupportWalk.next T s i)
    hnd hs (CanonicalSupportWalk.next_unique T s i hunique).1

end DualTree.ImmediateSupportHeight
