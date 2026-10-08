import DualTree.LiteralFrontierCleanup

/-!
# Intrinsic heights along a finite support branch

The intrinsic height of a support node is the number of its proper
support predecessors. On any support branch, this height increases
strictly. In particular, two support predecessors of a common
ambient node at equal intrinsic height coincide.

This is the rank ingredient for bounding the height of the
inclusive-cut frontiers in Lemma 27. No skewness is required for
either result.
-/

namespace DualTree.SupportHeightRanks

/-- Pointwise Boolean containment gives a filter-length bound. -/
private theorem filter_length_le
    {β : Type*} (xs : List β) (p q : β → Bool)
    (hpq : ∀ u, p u = true → q u = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil =>
      simp
  | cons a as ih =>
      have ha := hpq a
      cases pa : p a <;> cases qa : q a <;>
        simp [List.filter_cons, pa, qa] at ha ⊢ <;> omega

/-- A strict Boolean containment witnessed in the list gives strict length. -/
private theorem filter_length_lt
    {β : Type*} (xs : List β) (p q : β → Bool)
    (hpq : ∀ u, p u = true → q u = true)
    (hw : ∃ u, u ∈ xs ∧ p u = false ∧ q u = true) :
    (xs.filter p).length < (xs.filter q).length := by
  induction xs with
  | nil =>
      rcases hw with ⟨u, hu, _, _⟩
      simp at hu
  | cons a as ih =>
      rcases hw with ⟨u, hu, hpu, hqu⟩
      rcases List.mem_cons.mp hu with heq | hrest
      · subst u
        have hle := filter_length_le as p q hpq
        simpa [List.filter_cons, hpu, hqu] using Nat.lt_succ_of_le hle
      · have hlt := ih ⟨u, hrest, hpu, hqu⟩
        have ha := hpq a
        cases pa : p a <;> cases qa : q a <;>
          simp [List.filter_cons, pa, qa] at ha ⊢ <;> omega

/-- Strict support prefixes have strictly increasing intrinsic height. -/
theorem heightAt_lt_of_strictPrefix {b : Nat}
    (T : List (Node b)) {s t : Node b}
    (hs : s ∈ T) (hst : IsStrictPrefix s t) :
    SkewTree.heightAt T s < SkewTree.heightAt T t := by
  unfold SkewTree.heightAt SkewTree.preds
  apply filter_length_lt T
    (fun u => SkewTree.strictPrefixB u s)
    (fun u => SkewTree.strictPrefixB u t) ?_ ?_
  · intro u hu
    have hus : IsStrictPrefix u s :=
      (SkewBranchGeometry.strictPrefixB_iff u s).1 hu
    have hut : IsStrictPrefix u t := by
      refine ⟨isPrefix_trans hus.1 hst.1, ?_⟩
      intro heq
      have hlenus :=
        MeetClosedFromBranching.length_lt_of_strictPrefix hus
      have hlenst :=
        MeetClosedFromBranching.length_lt_of_strictPrefix hst
      rw [heq] at hlenus
      omega
    exact (SkewBranchGeometry.strictPrefixB_iff u t).2 hut
  · refine ⟨s, hs, ?_,
      (SkewBranchGeometry.strictPrefixB_iff s t).2 hst⟩
    simp [SkewTree.strictPrefixB]

/-- Equal intrinsic heights on one support branch identify the nodes. -/
theorem heightAt_injective_on_common_path {b : Nat}
    (T : List (Node b)) {s t x : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hsx : IsPrefix s x) (htx : IsPrefix t x)
    (heq : SkewTree.heightAt T s = SkewTree.heightAt T t) :
    s = t := by
  rcases le_total s.length t.length with hle | hle
  · have hst : IsPrefix s t :=
      CutFrontier.prefix_of_prefix_length_le hsx htx hle
    by_cases hsame : s = t
    · exact hsame
    · have hlt : SkewTree.heightAt T s < SkewTree.heightAt T t :=
        heightAt_lt_of_strictPrefix T hs ⟨hst, hsame⟩
      omega
  · have hts : IsPrefix t s :=
      CutFrontier.prefix_of_prefix_length_le htx hsx hle
    by_cases hsame : t = s
    · exact hsame.symm
    · have hlt : SkewTree.heightAt T t < SkewTree.heightAt T s :=
        heightAt_lt_of_strictPrefix T ht ⟨hts, hsame⟩
      omega

end DualTree.SupportHeightRanks
