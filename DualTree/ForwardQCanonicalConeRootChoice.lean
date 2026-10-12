import DualTree.ForwardQVisibleRootCapacity

/-!
# Existence of an aligned genuine-cone-root assignment

The preceding visibility theorem says that a genuine local variable
may occur inside the complete-support frontier cone i only if some
old source variable root lies strictly above that frontier.

This file proves the CONVERSE at the level of existence of a legal
decoded output variable word, without inventing a spanning property:
if the raw local cone words contain no genuine variable symbols in
cones with empty visible-root lists, choose the first visible old
source root for EVERY local variable name in each nonempty cone.
Use the actual source cut variable as a harmless unused fallback
at empty cones. This gives a legal full-frontier ConeData with the
explicit auxiliary R_i already verified.

Hence the precise obstruction to mere EXISTENCE of a root-aligned
cone-variable assignment is the presence of a local variable in a
cone with no visible old source variable root.

IMPORTANT: this canonical choice collapses every distinct local
cone-variable name within one frontier to the SAME old variable!
It is unsuitable as a drop-in proof of the paper's span/refinement
or preservation of independent local Hales--Jewett variables.
The resulting construction is an algebraic witness and a diagnostic.
-/

namespace DualTree.ForwardQCanonicalConeRootChoice

open ForwardSourceQTree
open ForwardQVisibleAncestorDecoder
open ForwardQConeVariableVisibility

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The actual final source cut belongs to the original
interior, so it carries a genuine source variable. -/
noncomputable def cutVariable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    c.source.word.Vars :=
  Classical.choose
    (StarredSignature.variable_at_interior
      c.source c.cut c.hcut)

/-- Even the empty-visible-frontier fallback is a genuinely
typed old source variable (but must never be used there). -/
theorem cutVariable_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    (cutVariable c).1.1 = c.cut :=
  (Classical.choose_spec
    (StarredSignature.variable_at_interior
      c.source c.cut c.hcut)).1

/-- The explicit canonical, generally non-injective root
assignment for every complete-support frontier. When there
is a visible root, choose the first one; otherwise choose
the old cut variable only as an unused default. -/
noncomputable def firstVisibleConeRoot
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α) :
    Index c → κ → c.source.word.Vars := by
  classical
  exact fun i _ =>
    if hpos : 0 < (visibleList c i).length then
      visibleVariable c i ⟨0, hpos⟩
    else cutVariable c

/-- On a cone with a visible root, the root selected by the
canonical assignment is genuinely present in the checked
visible list, rather than merely prefix-comparable. -/
theorem firstVisibleConeRoot_visible
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (i : Index c) (z : κ)
    (hpos : 0 < (visibleList c i).length) :
    (firstVisibleConeRoot c i z).1.1 ∈ visibleList c i := by
  classical
  have hroot :
      (firstVisibleConeRoot c i z).1.1 =
        (visibleList c i).get
          (⟨0, hpos⟩ : Fin (visibleList c i).length) := by
    simp [firstVisibleConeRoot, hpos,
      ForwardQVisibleRootCapacity.visibleVariable_root_eq_get]
  rw [hroot]
  exact List.get_mem _ _

/-- The canonical root assignment is fibrewise CONSTANT
on each frontier cone. This explicit loss of independence
must not be disguised as a span-preserving map. -/
theorem firstVisibleConeRoot_constant
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (i : Index c) (z w : κ) :
    firstVisibleConeRoot c i z =
      firstVisibleConeRoot c i w := rfl

/-- Exact source-facing condition for the EXISTENCE of some
root-aligned cone-variable transport: a genuine local variable
must never occur in a frontier cone whose visible-root list
is empty. No condition on unused local variable names. -/
def VariablesOnlyInVisibleCones
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ) : Prop :=
  ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
    raw i t = Sum.inr z →
      0 < (visibleList c i).length

/-- The canonical first-visible-variable choice satisfies
the real genuine-variable root-prefix condition under
the exact nonempty-visibility condition at occurrences. -/
theorem firstVisibleConeRoot_aligned
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (hvisible : VariablesOnlyInVisibleCones c raw) :
    ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (firstVisibleConeRoot c i z).1.1 t.1 := by
  intro i t z hfront hraw
  have hpos : 0 < (visibleList c i).length :=
    hvisible i t z hfront hraw
  have hv := firstVisibleConeRoot_visible c i z hpos
  have hstrict :=
    (sourceRoot_visible_iff_strict_frontier c i
      (firstVisibleConeRoot c i z)).1 hv
  exact isPrefix_trans hstrict.1 hfront

/-- Root-aligned transport EXISTS if and only if variables
occur only where a visible old source root is available.
Sufficiency uses the explicit first-visible-root assignment;
necessity is the kernel-checked visibility obstruction. -/
theorem exists_alignedConeRoot_iff
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ) :
    (∃ root : Index c → κ → c.source.word.Vars,
      ∀ (i : Index c) (t : BoundedNode b n) (z : κ),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        raw i t = Sum.inr z →
        IsPrefix (root i z).1.1 t.1) ↔
      VariablesOnlyInVisibleCones c raw := by
  constructor
  · rintro ⟨root, halign⟩ i t z hfront hraw
    have hv :
        (root i z).1.1 ∈ visibleList c i :=
      (coneRoot_aligned_iff_visible_at_occurrences c raw root).1
        halign i t z hfront hraw
    by_cases hpos : 0 < (visibleList c i).length
    · exact hpos
    · have hempty : visibleList c i = [] := by
        cases hs : visibleList c i with
        | nil => exact hs
        | cons a xs =>
            have hh : 0 < (visibleList c i).length := by
              simp [hs]
            exact False.elim (hpos hh)
      simp [hempty] at hv
  · intro hvisible
    exact ⟨firstVisibleConeRoot c,
      firstVisibleConeRoot_aligned c raw hvisible⟩

/-- A completely explicit legal full-frontier three-way ConeData
using the real visible-ancestor decoder R_i and the canonical
first-visible-root assignment. The only combinatorial hypothesis
is the EXACT no-variable-in-invisible-cones condition. -/
noncomputable def coneData
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (hvisible : VariablesOnlyInVisibleCones c raw) :
    ForwardQFullFrontierThreeWay.ConeData c (Fin (m + 1)) κ :=
  ForwardQVisibleAncestorDecoder.coneData c fallback raw
    (firstVisibleConeRoot c)
    (firstVisibleConeRoot_aligned c raw hvisible)

/-- The explicit legal word built from first-visible roots
retains exactly the corrected starred Q support, but need
not preserve the independent-variable span of the raw words. -/
theorem coneData_actual_Q_tree
    {b n l k m : Nat} {α κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (hvisible : VariablesOnlyInVisibleCones c raw) :
    ((coneData c fallback raw hvisible).onActualStarredQ
        hb c x hTbound).tree =
      (nodes c x.1).toList := by
  exact (coneData c fallback raw hvisible).onActualStarredQ_tree
    hb c x hTbound

end DualTree.ForwardQCanonicalConeRootChoice
