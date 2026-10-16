import DualTree.ForwardQFinalVectorOrdering

/-!
# The EXACT rank-truncation in Lemma 27's final ambient support T'

The printed formula on page 29 of Todorcevic–Tyros does not take
EVERY local coordinate variable root. It selects P_i(z) only if

    h_ws(f_i)(z) + h_T(frontier_i) < M,

where M denotes the height of the FINAL desired complete skew
support, not the earlier height m0 = h_T(cut).
Dropping this filter changes the statement, since corrected
forward frontier T-ranks can differ by one.

The previously checked candidateSupport retained ALL projected
local roots: it is an upper envelope. This module builds the
literal FILTERED support using the post-Ramsey mixed word's
actual coordinate support levels and the true ambient T
frontier heights.

The exact filtered support:
  - is a finite subset of the earlier unfiltered candidate;
  - belongs to T and retains the distinguished cut and every
    old source-variable root;
  - keeps the retained/new parts disjoint;
  - is monotone in the new TARGET height M.

These are safe set-level properties. We DO NOT infer that this
support is complete skew, or that its intrinsic height equals
the target M, from set containment alone. The remaining gluing
lemma must identify its OWN intrinsic levels and branch lengths.
-/

namespace DualTree.ForwardQFinalHeightBudget

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut

/-- The paper's literal height budget: local intrinsic
component-support rank PLUS the actual ambient T frontier
rank, strictly below the desired FINAL height M. -/
def FitsTargetHeight
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (u : LocalAddress c) : Prop :=
  SkewTree.heightAt
      (f.vector.components u.1).toVariableWord.supportNodes u.2.1 +
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1 < M

/-- Genuine tagged coordinate variable roots satisfying the
paper's rank cutoff. This is NOT the set of every local root. -/
noncomputable def selectedLocalRoots
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) : Finset (LocalAddress c) := by
  classical
  exact (taggedLocalRoots c f).filter (FitsTargetHeight c f M)

/-- Exact membership includes BOTH being a genuine variable
root of a coordinate word and satisfying the rank budget. -/
theorem selectedLocalRoots_mem_iff
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (u : LocalAddress c) :
    u ∈ selectedLocalRoots c f M ↔
      u ∈ taggedLocalRoots c f ∧ FitsTargetHeight c f M u := by
  classical
  simp [selectedLocalRoots]

/-- The selected tags are a finite SUBSET of the already
verified global injectable domain. -/
theorem selectedLocalRoots_subset_tagged
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) :
    selectedLocalRoots c f M ⊆ taggedLocalRoots c f := by
  intro u hu
  exact ((selectedLocalRoots_mem_iff c f M u).1 hu).1

/-- Raising the desired final height never removes a
previously admissible local tagged variable root. -/
theorem selectedLocalRoots_mono_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    {M N : Nat} (hMN : M ≤ N) :
    selectedLocalRoots c f M ⊆ selectedLocalRoots c f N := by
  intro u hu
  obtain ⟨htag, hbudget⟩ :=
    (selectedLocalRoots_mem_iff c f M u).1 hu
  apply (selectedLocalRoots_mem_iff c f N u).2
  refine ⟨htag, ?_⟩
  exact lt_of_lt_of_le hbudget hMN

/-- The literal projected set of NEW roots of the eventual
ambient f': a rank-filtered image in the actual complete T. -/
noncomputable def selectedProjectedRoots
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) : Finset (Node b) := by
  classical
  exact (selectedLocalRoots c f M).image
    (fun u => (projected c u).1)

/-- In particular the selected projections form a subset
of the unfiltered ambient root family. -/
theorem selectedProjectedRoots_subset_unfiltered
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) :
    selectedProjectedRoots c f M ⊆ projectedLocalRoots c f := by
  classical
  intro t ht
  obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp ht
  apply Finset.mem_image.mpr
  exact ⟨u, selectedLocalRoots_subset_tagged c f M hu, htu⟩

/-- Every selected projected ambient root carries its
ACTUAL originating frontier/tag and the printed rank budget.
No arbitrary enumeration or old-root Hall matching appears. -/
theorem selectedProjectedRoots_budget_witness
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b)
    (ht : t ∈ selectedProjectedRoots c f M) :
    ∃ u : LocalAddress c,
      u ∈ taggedLocalRoots c f ∧
      t = (projected c u).1 ∧ FitsTargetHeight c f M u := by
  classical
  obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp ht
  obtain ⟨htag, hbudget⟩ :=
    (selectedLocalRoots_mem_iff c f M u).1 hu
  exact ⟨u, htag, htu.symm, hbudget⟩

/-- The height-BUDGETED final ambient support T' from the paper,
expressed with repaired forward cut/frontier coordinates.
The unfiltered candidateSupport is only its upper envelope. -/
noncomputable def finalBudgetSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) : Finset (Node b) :=
  retained c ∪ selectedProjectedRoots c f M

/-- The printed support is a sub-support of the previously
kernel-checked unfiltered candidate; this does NOT imply
skewness or the correct complete height by itself. -/
theorem finalBudgetSupport_subset_unfiltered
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) :
    finalBudgetSupport c f M ⊆ candidateSupport c f := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with hret | hselected
  · exact Finset.mem_union.mpr (Or.inl hret)
  · exact Finset.mem_union.mpr
      (Or.inr (selectedProjectedRoots_subset_unfiltered
        c f M hselected))

/-- Each root in the exact height-filtered support remains
an actual old complete-support T vertex. -/
theorem finalBudgetSupport_subset_T
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f M) :
    t ∈ c.T :=
  candidateSupport_subset_T c f t
    (finalBudgetSupport_subset_unfiltered c f M ht)

/-- Retained initial T roots never collide with rank-filtered
projected roots: the proof is independent of final height. -/
theorem finalBudgetSupport_disjoint_retained
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) :
    Disjoint (retained c) (selectedProjectedRoots c f M) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hret hselected
  have hunfiltered :=
    selectedProjectedRoots_subset_unfiltered c f M hselected
  exact (Finset.disjoint_left.mp
    (retained_disjoint_projectedLocalRoots c f)) hret hunfiltered

/-- The final height filter never removes the distinguished
cut t0, because the entire retained portion is unchanged. -/
theorem cut_mem_finalBudgetSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat) :
    c.cut ∈ finalBudgetSupport c f M := by
  classical
  exact Finset.mem_union.mpr (Or.inl (cut_mem_retained c))

/-- The source signature variables remain available under any
target rank budget; new roots are added only outside the cut. -/
theorem old_source_root_mem_finalBudgetSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (v : c.source.word.Vars) :
    v.1.1 ∈ finalBudgetSupport c f M := by
  classical
  exact Finset.mem_union.mpr (Or.inl
    (old_source_root_mem_retained c v))

/-- Increasing final target height can only enlarge the
exact finite final support, keeping all old and new roots. -/
theorem finalBudgetSupport_mono_target
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    {M N : Nat} (hMN : M ≤ N) :
    finalBudgetSupport c f M ⊆ finalBudgetSupport c f N := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with hret | hselected
  · exact Finset.mem_union.mpr (Or.inl hret)
  · obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp hselected
    have hnew : t ∈ selectedProjectedRoots c f N :=
      Finset.mem_image.mpr
        ⟨u, selectedLocalRoots_mono_target c f hMN hu, htu⟩
    exact Finset.mem_union.mpr (Or.inr hnew)

end DualTree.ForwardQFinalHeightBudget
