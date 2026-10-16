import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQVisibleAncestorDecoder

/-!
# Lemma 27: the new variable roots of the FINAL refinement

The printed proof has TWO different stages.  Its Q maps ordinary
MIXED-PRODUCT ELEMENTS to starred words with the old source
interior roots.  After the mixed Ramsey theorem supplies coordinate
variable words (f_i), the proof constructs an ambient refined word
f' whose NEW variable roots are P_i(z), for z in ws(f_i).

Those new roots belong to the large complete ambient support T,
NOT to the l old variables of the intermediate Q-word.  Therefore
one must not assume a global Hall matching from all independently
tagged local variables into the old source interior: it can fail
by the old-root cardinality bound and is not the construction
described on page 29 of arXiv:2207.14599v1.

Here we prove the geometric transport needed for f':
  * the canonical projection P_i is injective on local addresses;
  * projections from distinct outside-cut frontier cones are disjoint;
  * projected local variable roots lie in the actual complete T;
  * they never coincide with old source variable roots;
  * arbitrary coordinate variable words determine a concrete
    FINITE set of jointly injected projected root positions.

All assertions use the corrected forward-auxiliary order and the
safe common local tail height k-(m+1).  The final support's complete
skew properties, full word f', and its [S,f'] containment still need
separate proofs; no Hall or Ramsey hypothesis is hidden here.
-/

namespace DualTree.ForwardQFinalRefinementRoots

open ForwardSourceQTree
open ForwardQActualCoordinateWord

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- A genuine local address tagged with its OWN sorted D0/D2 frontier. -/
abbrev LocalAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  Σ _ : Index c, BoundedNode b (k - (m + 1))

/-- Unlike a decoded Q-variable name, an ambient projected local
address is placed directly into the large complete tree T. -/
noncomputable def projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    {t : Node b // t ∈ c.T} :=
  projectLocal c u.1 u.2

theorem projected_mem_T
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    (projected c u).1 ∈ c.T :=
  (projected c u).2

theorem projected_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1
      (projected c u).1 :=
  projectLocal_cone c u.1 u.2

/-- Local address recovery is exact: equality of two projected
nodes at the SAME frontier forces equality of the original tails.
No assumption about their ambient lengths is needed. -/
theorem projectLocal_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    Function.Injective (projectLocal c i) := by
  intro z w hzw
  have hinv : 
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++ z.1 =
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++ w.1 := by
    calc
      (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon
          (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++ z.1 =
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon (projectLocal c i z)).1 :=
            (projectLocal_inverse c i z).symm
      _ = (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon (projectLocal c i w)).1 :=
            congrArg (fun v : {t : Node b // t ∈ c.T} =>
              (ForwardCompleteBijection.inverseAddress
                c.T c.hcomplete c.hnon v).1) hzw
      _ = (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon
          (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++ w.1 :=
            projectLocal_inverse c i w
  exact Subtype.ext (List.append_cancel_left hinv)

/-- Distinct frontier labels cannot project to the same T node.
At a fixed frontier, equality reduces to the previous inverse
address calculation. This is GLOBAL injectivity on the tagged
local address type, not a matching to OLD variables. -/
theorem projected_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Injective (projected c) := by
  rintro ⟨i,z⟩ ⟨j,w⟩ h
  change projectLocal c i z = projectLocal c j w at h
  have hij : i = j := by
    by_contra hne
    have hleft : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1
        (projectLocal c i z).1 :=
      projectLocal_cone c i z
    have hright : IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1
        (projectLocal c i z).1 := by
      have hr := projectLocal_cone c j w
      rw [congrArg Subtype.val h]
      exact hr
    exact (ForwardQFullFrontierWord.frontier_cones_disjoint
      c i j hne (projectLocal c i z).1) ⟨hleft, hright⟩
  subst j
  have hzw : z = w := projectLocal_injective c i h
  subst w
  rfl

/-- Prefixes of local addresses remain prefixes of their
actual projected ambient T vertices in the same cone. -/
theorem projected_same_frontier_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k - (m + 1)))
    (hzw : IsPrefix z.1 w.1) :
    IsPrefix (projected c ⟨i,z⟩).1 (projected c ⟨i,w⟩).1 :=
  ForwardUniformConeDomains.projectCommon_prefix
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i)
    z w hzw

/-- No projected NEW variable root collides with any retained
old source variable root. All old roots occur BEFORE the cut,
whereas every projected local node is in a frontier cone
outside the cut. -/
theorem projected_ne_old_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c)
    (v : c.source.word.Vars) :
    (projected c u).1 ≠ v.1.1 := by
  intro heq
  have hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut u.1).1
      v.1.1 := by
    rw [← heq]
    exact projected_cone c u
  exact (ForwardQFullFrontierWord.frontier_cone_avoids_source_root
    c u.1 v) hfront

/-- Type of the output of the MIXED PRODUCT Ramsey step, with
the genuinely correct local height and no artificial Hall data.
β can be the enlarged alphabet of Lemma 27. -/
abbrev LocalMixedWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Nat) (β : Type*) :=
  MixedProduct.VariableWord b (k - (m + 1))
    (ForwardSortedFrontiers.frontiers c.T c.cut).length
    q β (SkewTree.forwardAuxB (b := b)) (kind c)

/-- The tagged local variable ROOTS occurring in the coordinate
words f_i. This is a finite subset of ALL possible local
addresses, not the old source-word variable type. -/
noncomputable def taggedLocalRoots
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    Finset (LocalAddress c) := by
  classical
  exact (Finset.univ : Finset (Index c)).biUnion (fun i =>
    (f.vector.components i).support.toFinset.image
      (fun z => (⟨i,z⟩ : LocalAddress c)))

/-- The ACTUAL NEW projected ambient roots for the final f'
construction. This set lives in T, not in the l-element
interior variable set of the intermediate Q word. -/
noncomputable def projectedLocalRoots
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    Finset (Node b) := by
  classical
  exact (taggedLocalRoots c f).image
    (fun u => (projected c u).1)

/-- The final refinement's new roots are all actual complete
ambient-support vertices. -/
theorem projectedLocalRoots_subset_T
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    ∀ t, t ∈ projectedLocalRoots c f → t ∈ c.T := by
  classical
  intro t ht
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
  exact projected_mem_T c u

/-- The new projected-root set is disjoint from the retained
source variable roots, even if several local component words
use the same local variable *name*. Distinct FRONTIER tags
have already been proved injective above. -/
theorem projectedLocalRoots_disjoint_old
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β) :
    Disjoint (projectedLocalRoots c f)
      c.source.word.supportNodes.toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hsource
  obtain ⟨u, _, hproj⟩ := Finset.mem_image.mp ht
  have hsourceNode :
      (projected c u).1 ∈ c.source.word.supportNodes := by
    rw [hproj]
    exact List.mem_toFinset.mp hsource
  obtain ⟨v, hv⟩ :=
    ForwardQVisibleAncestorDecoder.exists_variable_at_support_root
      c (projected c u).1 hsourceNode
  exact (projected_ne_old_source_root c u v) hv.symm

end DualTree.ForwardQFinalRefinementRoots
