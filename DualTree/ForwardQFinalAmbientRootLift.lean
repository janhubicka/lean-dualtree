import DualTree.RootCompatibleRefinement
import DualTree.ForwardQFinalCompleteSkew
import DualTree.ForwardQAmbientFibreFrame

/-!
# Lifting the corrected final Lemma 27 support to ambient word roots

The selected final support consists of nodes in the original complete T,
but the original ambient variable word is indexed by *bounded* nodes
of the homogeneous b-ary tree. This module constructs the exact
bounded-root list without changing membership or introducing duplicated
roots. It is independent of any alphabet-size restriction.

A FibreFrame witnesses that the original ambient variable word f has
exactly the T roots. The selected final root list is thus a subset of
the roots of f and contains the ambient T root, which prefixes every
original variable root. The generic root-compatible substitution
construction therefore yields a genuine coarsening of f with precisely
the selected roots and evaluated span contained in span(f).

IMPORTANT: The coarsening below is deliberately coarse and generally
NOT the prescribed post-Ramsey word f' from Lemma 27. It does not yet
agree with the local mixed-product variable words on the selected
frontier fibres. This module isolates the bounded-subtype and span
obligations so that a subsequent Q-compatible substitution can reuse
them without ad hoc casts or accidental unsupported root names.
-/

namespace DualTree.ForwardQFinalAmbientRootLift

open ForwardSourceQTree
open ForwardQFinalHeightBudget
open ForwardQFinalRefinementRoots

/-- Each selected final support vertex has an exact bounded
ambient-word position, by inclusion in the original T. -/
noncomputable def boundedFinalSet
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    Finset (BoundedNode b n) := by
  classical
  exact (finalBudgetSupport g.core f (m+q)).attach.image
    (fun u =>
      (⟨u.1, g.T_bounded u.1
        (finalBudgetSupport_subset_T g.core f (m+q) u.1 u.2)⟩ :
          BoundedNode b n))

/-- Membership in the bounded final-root set is EXACTLY
membership of the raw node in the corrected final support. -/
theorem mem_boundedFinalSet_iff
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (s : BoundedNode b n) :
    s ∈ boundedFinalSet g f ↔
      s.1 ∈ finalBudgetSupport g.core f (m+q) := by
  classical
  unfold boundedFinalSet
  constructor
  · intro hs
    obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hs
    have hval : u.1 = s.1 := congrArg Subtype.val hEq
    simpa only [hval] using u.2
  · intro hs
    let u : {t : Node b // t ∈ finalBudgetSupport g.core f (m+q)} :=
      ⟨s.1, hs⟩
    apply Finset.mem_image.mpr
    refine ⟨u, by simp, ?_⟩
    apply Subtype.ext
    rfl

/-- The root list for the eventual ambient word f' retains the
exact support set and inherits automatic duplicate-freeness. -/
noncomputable def boundedFinalRoots
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    List (BoundedNode b n) :=
  (boundedFinalSet g f).toList

theorem boundedFinalRoots_nodup
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    (boundedFinalRoots g f).Nodup :=
  Finset.nodup_toList (boundedFinalSet g f)

theorem mem_boundedFinalRoots_iff
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (s : BoundedNode b n) :
    s ∈ boundedFinalRoots g f ↔
      s.1 ∈ finalBudgetSupport g.core f (m+q) := by
  exact (Finset.mem_toList).trans (mem_boundedFinalSet_iff g f s)

/-- Every proposed final root is actually an ORIGINAL
ambient-variable root of the given FibreFrame. -/
theorem boundedFinalRoots_subset_original
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (v : {t // t ∈ boundedFinalRoots g f}) :
    v.1 ∈ g.ambient.support := by
  have hs :
      v.1.1 ∈ finalBudgetSupport g.core f (m+q) :=
    (mem_boundedFinalRoots_iff g f v.1).1 v.2
  exact (g.ambient_support_T v.1).2
    (finalBudgetSupport_subset_T g.core f (m+q) v.1.1 hs)

/-- The complete T root is bounded by n, hence is an actual
homogeneous ambient-word position. -/
noncomputable def boundedAmbientRoot
    {b n l k m : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α) :
    BoundedNode b n :=
  ⟨ForwardCompleteEmbedding.rootOf g.core.T
      g.core.hcomplete g.core.hnon,
    g.T_bounded _
      (ForwardCompleteEmbedding.rootOf_mem
        g.core.T g.core.hcomplete g.core.hnon)⟩

/-- The original T root survives the exact rank filter and
belongs to the proposed bounded final word support. -/
noncomputable def finalRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    {t // t ∈ boundedFinalRoots g f} := by
  refine ⟨boundedAmbientRoot g, ?_⟩
  apply (mem_boundedFinalRoots_iff g f (boundedAmbientRoot g)).2
  exact Finset.mem_toList.mp
    (ForwardQFinalMeetClosure.ambient_root_mem_final g.core f)

/-- The original ambient complete-tree root prefixes every root
of the original ambient variable word, not only the selected roots. -/
theorem finalRoot_prefix_original
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : g.ambient.Vars) :
    IsPrefix (finalRoot g f).1.1 u.1.1 := by
  have hu : u.1.1 ∈ g.core.T :=
    (g.ambient_support_T u.1).1 u.2
  exact ForwardCompleteEmbedding.rootOf_prefix
    g.core.T g.core.hcomplete g.core.hnon u.1.1 hu

/-- A legal, coarse ambient word having EXACTLY the final
rank-budgeted roots, with an explicit root-compatible
syntactic substitution of the original ambient word. -/
noncomputable def coarseFinalWord
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    VariableWord b n α :=
  RootCompatibleRefinement.collapse
    g.ambient (boundedFinalRoots g f)
    (boundedFinalRoots_nodup g f)
    (boundedFinalRoots_subset_original g f)
    (finalRoot g f)
    (finalRoot_prefix_original g f)

/-- The coarse word has no extra roots: exactly the
corrected final support viewed as bounded ambient nodes. -/
theorem coarseFinalWord_support_iff
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (s : BoundedNode b n) :
    s ∈ (coarseFinalWord g f).support ↔
      s.1 ∈ finalBudgetSupport g.core f (m+q) := by
  change s ∈ boundedFinalRoots g f ↔ _
  exact mem_boundedFinalRoots_iff g f s

/-- Its evaluated span is contained in that of the ORIGINAL
ambient variable word, not merely in that of the old source
starred word. This does not yet give local Q compatibility. -/
theorem coarseFinalWord_span_subset
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    (coarseFinalWord g f).span ⊆ g.ambient.span :=
  RootCompatibleRefinement.collapse_span_subset
    g.ambient (boundedFinalRoots g f)
    (boundedFinalRoots_nodup g f)
    (boundedFinalRoots_subset_original g f)
    (finalRoot g f)
    (finalRoot_prefix_original g f)

end DualTree.ForwardQFinalAmbientRootLift
