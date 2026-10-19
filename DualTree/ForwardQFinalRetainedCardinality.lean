import DualTree.ForwardQFinalExtraRetainedObstruction
import DualTree.ForwardQFinalRetainedRanks

/-!
# Cut rank gives a cardinal obstruction to reverse Q-span coverage

The corrected final ambient support retains every original T vertex up to
the inclusive length-first forward cut t0.  Because the intrinsic height of
t0 in T is m, its m genuine strict T-predecessors are all retained, as is
t0 itself.  Thus at least m+1 distinct original f-variable roots survive.

The starred source word g' has exactly l variable roots: its support nodes
are precisely the l interiors of the source semi-complete tree.
Consequently, if l <= m, the retained part of T necessarily contains an
original ambient f root NOT belonging to the old source-variable support.

Over a two-letter alphabet that extra retained root causes the *verified*
conditional obstruction from ForwardQFinalExtraRetainedObstruction:
f' has an evaluation not representable by any evaluated corrected
fibrewise Q(w), even with arbitrary enlarged mixed-product input w.

This is a concrete unconditional-on-the-substitution noncoverage result
under the simple numerical hypothesis l <= m.  It concerns the particular
corrected forward-Q and f' construction, NOT the existence conclusion of
Lemma 27 or the whole Dual Ramsey Theorem.  It also cannot be used to
identify the printed reverse-starred W_* with the corrected domain.
-/

namespace DualTree.ForwardQFinalRetainedCardinality

open ForwardSourceQTree
open ForwardQFinalSupportCut
open ForwardQFinalRetainedRanks
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift

/-- Exactly m retained vertices strictly precede the genuine cut:
their rank is inherited from the ambient complete T support. -/
theorem cut_retained_predecessor_count
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    ((retained c).filter
      (fun t => SkewTree.strictPrefixB t c.cut = true)).card = m := by
  calc
    ((retained c).filter
      (fun t => SkewTree.strictPrefixB t c.cut = true)).card =
        SkewTree.heightAt (retained c).toList c.cut :=
      (heightAt_finset_eq_card (retained c) c.cut).symm
    _ = SkewTree.heightAt c.T c.cut :=
      retained_heightAt_eq_ambientT c c.cut
        (cut_mem_retained c)
    _ = m := c.hm

/-- The m strict predecessors plus the cut itself supply
at least m+1 DISTINCT vertices to the retained ambient support. -/
theorem cut_rank_add_one_le_retained_card
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    m + 1 ≤ (retained c).card := by
  classical
  let P := (retained c).filter
    (fun t => SkewTree.strictPrefixB t c.cut = true)
  have hcutNot : c.cut ∉ P := by
    intro hcut
    have hs : IsStrictPrefix c.cut c.cut :=
      (SkewBranchGeometry.strictPrefixB_iff c.cut c.cut).1
        (Finset.mem_filter.mp hcut).2
    exact hs.2 rfl
  have hsub : insert c.cut P ⊆ retained c := by
    intro t ht
    rcases Finset.mem_insert.mp ht with heq | hp
    · subst t
      exact cut_mem_retained c
    · exact (Finset.mem_filter.mp hp).1
  have hcard : (insert c.cut P).card ≤ (retained c).card :=
    Finset.card_le_card hsub
  have hcount : P.card = m :=
    cut_retained_predecessor_count c
  have hcardInsert : (insert c.cut P).card = P.card + 1 := by
    simp [hcutNot]
  rw [hcardInsert, hcount] at hcard
  omega

/-- If the number of retained T nodes exceeds l, at least one
of them is absent from the old starred source-variable support.
This uses the actual source support/interior equivalence and
the source's l-interior count, not a guessed Hall map. -/
theorem exists_extra_retained_of_card_gt_l
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (hcard : l < (retained c).card) :
    ∃ t : Node b,
      t ∈ retained c ∧
      t ∉ c.source.word.supportNodes := by
  classical
  by_contra hno
  have hsubset : retained c ⊆
      (SkewTree.interior c.source.tree).toFinset := by
    intro t ht
    have hsource : t ∈ c.source.word.supportNodes := by
      by_contra hn
      exact hno ⟨t, ht, hn⟩
    have hinterior : t ∈ SkewTree.interior c.source.tree :=
      (c.source.support_eq_interior t).1 hsource
    exact List.mem_toFinset.mpr hinterior
  have hle : (retained c).card ≤
      (SkewTree.interior c.source.tree).toFinset.card :=
    Finset.card_le_card hsubset
  have hsourceCard :
      (SkewTree.interior c.source.tree).toFinset.card ≤ l := by
    calc
      (SkewTree.interior c.source.tree).toFinset.card ≤
          (SkewTree.interior c.source.tree).length :=
        List.toFinset_card_le _
      _ = l := c.source.interior_card
  omega

/-- The entirely source-facing counting condition l <= m
forces an actual early T root outside the source starred word. -/
theorem exists_extra_retained_of_l_le_cut_rank
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (hlm : l ≤ m) :
    ∃ t : Node b,
      t ∈ retained c ∧
      t ∉ c.source.word.supportNodes := by
  apply exists_extra_retained_of_card_gt_l c
  have hcard := cut_rank_add_one_le_retained_card c
  omega

/-- Under the numerical condition l <= m, the current corrected
final ambient word f' has an evaluation outside the union of ALL
actual corrected fibrewise Q-image evaluations.  Only the ordinary
two-letter alphabet distinction is needed; NO hypothesis on rho
identifying any particular pair of roots is added. -/
theorem not_every_final_evaluation_of_l_le_cut_rank
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (hlm : l ≤ m) :
    ∃ ψ : TreeWord b n α,
      ψ ∈ (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
        g f (fun x : α => x) fallback).span ∧
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
        (τ : g.core.source.word.Vars → α),
        SpanAudit.eval
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w) τ ≠ ψ := by
  obtain ⟨t,htRet,htNotOld⟩ :=
    exists_extra_retained_of_l_le_cut_rank g.core hlm
  let u := ForwardQAmbientFibreFrame.ambientAtTRoot
    g t (retained_subset_T g.core t htRet)
  have hu : ForwardAux u.1.1 g.core.cut :=
    (Finset.mem_filter.mp htRet).2
  have hnotold : u.1 ∉ g.core.source.word.support := by
    intro hs
    have hn : t ∈ g.core.source.word.supportNodes := by
      change t ∈ g.core.source.word.support.map (fun v => v.1)
      exact List.mem_map.mpr ⟨u.1,hs,rfl⟩
    exact htNotOld hn
  exact ForwardQFinalExtraRetainedObstruction.not_every_final_evaluation_of_extra_retained_root
    g f fallback hα u hu hnotold

end DualTree.ForwardQFinalRetainedCardinality
