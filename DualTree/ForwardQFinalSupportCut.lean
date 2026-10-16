import DualTree.ForwardQFinalRefinementRoots
import DualTree.ForwardQSourceTerminals
import DualTree.ForwardQConeVariableVisibility

/-!
# Lemma 27: the candidate support T' of the FINAL ambient word

The paper's final f' (after the mixed Ramsey theorem) retains all
complete-support roots at/before the distinguished cut t0 and adds
the projections P_i(z) of variable roots z of the chosen local
component words f_i.

The previous module shows P_i is jointly injective into the LARGE
ambient complete support T, independently of Hall matching into the
much smaller source interior. Here we prove the exact set-level
gluing: retained and projected roots form DISJOINT finite sets in T.
Every retained source root is still present; no projection reenters
the inclusive forward cut; different frontier cones are separated.

We intentionally call this a CANDIDATE support. Membership and
disjointness do not themselves establish that the assembled support
is forward m-complete skew. The remaining complete-skew and
ambient-fibrewise f' construction are independent obligations.

The selected local height k-(m+1) is the certified uniformly safe
one for the corrected forward auxiliary order; the printed formula
needs rechecking rather than silently changing this index.
-/

namespace DualTree.ForwardQFinalSupportCut

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- Genuine complete ambient T nodes at or before the corrected
INCLUSIVE forward cut. The cut itself is retained. -/
noncomputable def retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Finset (Node b) := by
  classical
  exact c.T.toFinset.filter (fun t => ForwardAux t c.cut)

/-- Every retained node belongs to the complete support T. -/
theorem retained_subset_T
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ retained c) :
    t ∈ c.T := by
  classical
  exact List.mem_toFinset.mp (Finset.mem_filter.mp ht).1

/-- Relative prefix closure of the retained portion, amongst
the actual T nodes: an earlier T ancestor cannot lie past cut
when one of its T descendants lies at/before the cut. -/
theorem retained_prefix_closed_in_T
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ c.T)
    (ht : t ∈ retained c)
    (hst : IsPrefix s t) :
    s ∈ retained c := by
  classical
  have hbefore : ForwardAux t c.cut :=
    (Finset.mem_filter.mp ht).2
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr hs,
      ForwardInclusiveFrontier.forwardAux_of_prefix hst hbefore⟩

/-- The distinguished original cut t0 is literally retained. -/
theorem cut_mem_retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    c.cut ∈ retained c := by
  classical
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr c.hcutT,
      CanonicalForwardAuxIso.forwardAux_refl c.cut⟩

/-- Every original source VARIABLE root remains in the
retained part of T'. This is not a Hall target condition:
the new projected roots do not have to map to these names. -/
theorem old_source_root_mem_retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (v : c.source.word.Vars) :
    v.1.1 ∈ retained c := by
  classical
  have hinterior :
      v.1.1 ∈ SkewTree.interior c.source.tree :=
    StarredSignature.variable_root_in_interior c.source v
  have hcut : ForwardAux v.1.1 c.cut := by
    simpa [SkewTree.forwardAuxB] using
      (c.hmax v.1.1 hinterior)
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr
      (ForwardQConeVariableVisibility.sourceRoot_mem_T c v),
      hcut⟩

/-- In fact every vertex of the previously checked Q old
signature base lies in the retained T portion. -/
theorem oldBase_mem_retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ oldBase c) :
    t ∈ retained c := by
  classical
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr
      (ForwardQFixedBase.oldBase_subset_complete c t ht),
      ForwardQSourceTerminals.literal_oldBase_before_cut c t ht⟩

/-- Every projected candidate new root lies STRICTLY outside
the corrected inclusive forward cut, in the precise sense of
failing the ForwardAux predicate. -/
theorem projected_outside_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    ¬ ForwardAux (projected c u).1 c.cut := by
  have hf :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut u.1
  exact ForwardInclusiveFrontier.outside_of_prefix
    hf.2.1 (projected_cone c u)

/-- No new projected root can be a prefix of an earlier
retained T vertex. The old vertices may, of course, be
ancestors of new roots; that is how the final support branches. -/
theorem projected_not_prefix_retained
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c)
    (t : Node b)
    (ht : t ∈ retained c) :
    ¬ IsPrefix (projected c u).1 t := by
  intro hp
  have hcut : ForwardAux t c.cut :=
    (Finset.mem_filter.mp ht).2
  exact (projected_outside_cut c u)
    (ForwardInclusiveFrontier.forwardAux_of_prefix hp hcut)

/-- Projected roots attached to DIFFERENT sorted frontiers
are mutually prefix-incomparable. This is much stronger than
inequality, and will be needed for proving the skew gluing. -/
theorem projected_incomparable_of_distinct_frontiers
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : LocalAddress c)
    (hij : u.1 ≠ v.1) :
    ¬ IsPrefix (projected c u).1 (projected c v).1 ∧
    ¬ IsPrefix (projected c v).1 (projected c u).1 := by
  constructor
  · intro hpre
    have hfirst : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1
        (projected c v).1 :=
      isPrefix_trans (projected_cone c u) hpre
    exact (ForwardQFullFrontierWord.frontier_cones_disjoint
      c u.1 v.1 hij (projected c v).1)
        ⟨hfirst, projected_cone c v⟩
  · intro hpre
    have hsecond : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut v.1).1
        (projected c u).1 :=
      isPrefix_trans (projected_cone c v) hpre
    exact (ForwardQFullFrontierWord.frontier_cones_disjoint
      c v.1 u.1 hij.symm (projected c u).1)
        ⟨hsecond, projected_cone c u⟩

/-- Set-level support proposed for the corrected final ambient
word f': exactly the prefix-cut portion of T plus the projected
variable roots from the post-Ramsey mixed variable word. -/
noncomputable def candidateSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    Finset (Node b) :=
  retained c ∪ projectedLocalRoots c f

/-- All candidate support vertices lie in the original complete
ambient T, which carries the root variables of f. -/
theorem candidateSupport_subset_T
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (t : Node b)
    (ht : t ∈ candidateSupport c f) :
    t ∈ c.T := by
  classical
  rcases Finset.mem_union.mp ht with hret | hproj
  · exact retained_subset_T c t hret
  · exact projectedLocalRoots_subset_T c f t hproj

/-- Old initial-cut and new projected root sets are disjoint,
by exact monotonicity of the inclusive corrected forward cut. -/
theorem retained_disjoint_projectedLocalRoots
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    Disjoint (retained c) (projectedLocalRoots c f) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hnew
  obtain ⟨u, _, hproj⟩ := Finset.mem_image.mp hnew
  have hbefore : ForwardAux t c.cut :=
    (Finset.mem_filter.mp ht).2
  have hbefore' : ForwardAux (projected c u).1 c.cut := by
    rw [hproj]
    exact hbefore
  exact (projected_outside_cut c u) hbefore'

/-- The original cut, and hence the full initial ambient
variable part, remains in the proposed final support. -/
theorem cut_mem_candidateSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    c.cut ∈ candidateSupport c f := by
  classical
  exact Finset.mem_union.mpr (Or.inl (cut_mem_retained c))

/-- Every actual old source variable root is still in the
candidate final support, while the independent new local tags
are projected directly into T and never forced to use old roots. -/
theorem old_source_root_mem_candidateSupport
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (v : c.source.word.Vars) :
    v.1.1 ∈ candidateSupport c f := by
  classical
  exact Finset.mem_union.mpr
    (Or.inl (old_source_root_mem_retained c v))

end DualTree.ForwardQFinalSupportCut
