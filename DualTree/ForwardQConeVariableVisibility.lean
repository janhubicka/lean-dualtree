import DualTree.ForwardQVisibleAncestorDecoder

/-!
# Necessary and sufficient visibility of genuine cone-variable roots

The forward-corrected Q word has exactly the old source-interior
variables. A genuine local cone variable occurring in the complete
support frontier cone rooted at f_i can therefore map to a source
variable v only when the root of v STRICTLY precedes f_i.

This module proves that necessity on the actual corrected frame, and
shows the converse: a source root selected from the visible ancestor
list is aligned with every occurrence inside that frontier cone.

Consequently the remaining cone-variable alignment premise in the
full-frontier three-way decoder is equivalent to the concrete finite
condition that every transported root is visible at every occurrence.
An empty visible list forbids the occurrence of ANY genuine variable
within that cone. This is not merely a type-level concern: replacing
local variable names by unrestricted source roots violates the
root-prefix axiom of the output variable word.

The statements do not construct the particular paper cone-variable
transport or prove that it preserves the mixed-product span.
-/

namespace DualTree.ForwardQConeVariableVisibility

open ForwardSourceQTree
open ForwardQFullFrontierWord
open ForwardQVisibleAncestorDecoder

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Every source variable root is a genuine T support vertex
because it is an old source interior node and S is contained in T. -/
theorem sourceRoot_mem_T
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (v : c.source.word.Vars) :
    v.1.1 ∈ c.T := by
  have hinterior : v.1.1 ∈ SkewTree.interior c.source.tree :=
    StarredSignature.variable_root_in_interior c.source v
  have hsource : v.1.1 ∈ c.source.tree :=
    (List.mem_filter.mp hinterior).1
  exact c.hST v.1.1 hsource

/-- The source-variable subtype really represents membership in the
literal list of old source variable roots. -/
theorem sourceRoot_mem_supportNodes
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (v : c.source.word.Vars) :
    v.1.1 ∈ c.source.word.supportNodes := by
  change v.1.1 ∈ c.source.word.support.map (fun t => t.1)
  exact List.mem_map.mpr ⟨v.1, v.2, rfl⟩

/-- If a source variable at root v occurs at a node t within
frontier cone i, its root is a STRICT ancestor of the frontier.
The reverse prefix direction is impossible because old source
roots lie before the final corrected forward cut. -/
theorem root_strict_frontier_of_occurrence
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (t : BoundedNode b n)
    (v : c.source.word.Vars)
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hroot : IsPrefix v.1.1 t.1) :
    IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  let f := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have hnot : ¬ IsPrefix f v.1.1 :=
    ForwardQFullFrontierWord.frontier_cone_avoids_source_root c i v
  have hlen : v.1.1.length ≤ f.length := by
    by_contra hn
    have hrev : f.length ≤ v.1.1.length := by omega
    exact hnot (CutFrontier.prefix_of_prefix_length_le
      hfront hroot hrev)
  have hpre : IsPrefix v.1.1 f :=
    CutFrontier.prefix_of_prefix_length_le hroot hfront hlen
  refine ⟨hpre, ?_⟩
  intro heq
  apply hnot
  rw [← heq]
  exact isPrefix_refl _

/-- A source variable root can occur within a full frontier
cone only if it belongs to the ACTUAL list of visible old
source-variable ancestors of that frontier. -/
theorem sourceRoot_mem_visible_of_occurrence
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (t : BoundedNode b n)
    (v : c.source.word.Vars)
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hroot : IsPrefix v.1.1 t.1) :
    v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i := by
  have hstrict :=
    root_strict_frontier_of_occurrence c i t v hfront hroot
  have hpred : v.1.1 ∈ SkewTree.preds c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
    unfold SkewTree.preds
    exact List.mem_filter.mpr
      ⟨sourceRoot_mem_T c v,
        (SkewBranchGeometry.strictPrefixB_iff _ _).2 hstrict⟩
  change v.1.1 ∈ (SkewTree.preds c.T
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1).filter
      (fun s => decide (s ∈ c.source.word.supportNodes))
  apply List.mem_filter.mpr
  refine ⟨hpred, ?_⟩
  simpa using sourceRoot_mem_supportNodes c v

/-- For an ACTUAL old source variable, being a visible ancestor
is equivalent to having a strictly preceding root along the
selected complete-support frontier. -/
theorem sourceRoot_visible_iff_strict_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (v : c.source.word.Vars) :
    v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i ↔
      IsStrictPrefix v.1.1
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  constructor
  · intro hv
    exact (ConeLocalDecoder.visibleAncestor_spec
      c.T c.source.word.supportNodes
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      v.1.1 hv).2.2
  · intro hstrict
    have hpred : v.1.1 ∈ SkewTree.preds c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
      unfold SkewTree.preds
      exact List.mem_filter.mpr
        ⟨sourceRoot_mem_T c v,
          (SkewBranchGeometry.strictPrefixB_iff _ _).2 hstrict⟩
    change v.1.1 ∈ (SkewTree.preds c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1).filter
        (fun s => decide (s ∈ c.source.word.supportNodes))
    exact List.mem_filter.mpr
      ⟨hpred, by simpa using sourceRoot_mem_supportNodes c v⟩

/-- Precisely the finite visible-root condition is equivalent to
the remaining genuine-cone-variable alignment field in the
all-frontier visible-ancestor decoder. The raw family is indexed
by ALL D0/D2 frontier coordinates. -/
theorem coneRoot_aligned_iff_visible_at_occurrences
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars) :
    (∀ (i : Index c) (t : BoundedNode b n) (z : κ),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        raw i t = Sum.inr z →
        IsPrefix (coneRoot i z).1.1 t.1) ↔
      (∀ (i : Index c) (t : BoundedNode b n) (z : κ),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        raw i t = Sum.inr z →
        (coneRoot i z).1.1 ∈
          ForwardQVisibleAncestorDecoder.visibleList c i) := by
  constructor
  · intro halign i t z hfront hraw
    exact sourceRoot_mem_visible_of_occurrence c i t
      (coneRoot i z) hfront (halign i t z hfront hraw)
  · intro hvisible i t z hfront hraw
    have hstrict :=
      (sourceRoot_visible_iff_strict_frontier c i (coneRoot i z)).1
        (hvisible i t z hfront hraw)
    exact isPrefix_trans hstrict.1 hfront

/-- If the actual visible old-root list is empty then no
genuine cone variable can appear inside this frontier cone in
ANY root-aligned three-way Q word. -/
theorem no_cone_variables_if_no_visible_roots
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (halign : ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1)
    (i : Index c)
    (hempty : ForwardQVisibleAncestorDecoder.visibleList c i = [])
    (t : BoundedNode b n)
    (z : κ)
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    raw i t ≠ Sum.inr z := by
  intro hraw
  have hv :=
    (coneRoot_aligned_iff_visible_at_occurrences c raw coneRoot).1
      halign i t z hfront hraw
  simp [hempty] at hv

/-- A per-cone root choice whose root is explicitly selected
from the visible source-variable list has the precise local
root-prefix property required by the three-way Q decoder. -/
theorem aligned_of_visible_root_choice
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hvisible : ∀ (i : Index c) (z : κ),
      (coneRoot i z).1.1 ∈
        ForwardQVisibleAncestorDecoder.visibleList c i) :
    ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1 :=
  (coneRoot_aligned_iff_visible_at_occurrences c raw coneRoot).2
    (fun i t z _ _ => hvisible i z)

/-- The actual corrected R_i and arbitrary cone-variable root map
assemble into a legal full-frontier ConeData under the FINITE
visibility-at-occurrences test, with no separate root-prefix
alignment assumption. -/
noncomputable def coneData_of_visible_roots
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hvisible : ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      (coneRoot i z).1.1 ∈
        ForwardQVisibleAncestorDecoder.visibleList c i) :
    ForwardQFullFrontierThreeWay.ConeData c (Fin (m + 1)) κ :=
  ForwardQVisibleAncestorDecoder.coneData c fallback raw coneRoot
    ((coneRoot_aligned_iff_visible_at_occurrences c raw coneRoot).2
      hvisible)

end DualTree.ForwardQConeVariableVisibility
