import DualTree.ForwardQConeVariableVisibility
import Mathlib

/-!
# Exact capacity of visible source-variable roots in one Q frontier cone

Once the full-frontier cone-variable root criterion has been reduced
to visibility, the list of available old source roots is a FINITE,
duplicate-free list of length at most m+1. It enumerates actual
source-variable subtype elements without loss or duplication.

Thus the corrected m+1 auxiliary decoder really reaches ALL old
source variables available at the frontier, not only an abstract
visible-index list.

There is also a genuine limitation on the unverified transport of
local cone variables: if m+2 DISTINCT local variables all occur in
the same frontier cone, no injective transport of those variable
names to visible source roots exists. The conclusion concerns
injectivity and independent variables, not whether the Ramsey
theorem can still be repaired using a quotient or another span.

The theorem follows from the actual forward-corrected source frame,
not a toy one-bullet abstract product, and uses no sorry axioms.
-/

namespace DualTree.ForwardQVisibleRootCapacity

open ForwardSourceQTree
open ForwardQVisibleAncestorDecoder
open ForwardQConeVariableVisibility

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The exact number of OLD variable roots available in a cone
is at most the m+1 auxiliary letters. -/
theorem visibleList_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    (ForwardQVisibleAncestorDecoder.visibleList c i).length ≤ m + 1 :=
  Lemma27Repair.visibleAncestors_length_le_aux
    c.T c.source.word.supportNodes
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1
    (ForwardQVisibleAncestorDecoder.frontier_height_le_m_succ c i)

/-- The visible roots are enumerated WITHOUT DUPLICATES,
since the enclosing genuine forward-complete support T is
duplicate-free and both predecessor and root restrictions
are literal filters of its finite vertex list. -/
theorem visibleList_nodup
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    (ForwardQVisibleAncestorDecoder.visibleList c i).Nodup := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hTnodup : c.T.Nodup := by simpa using hskew.1
  unfold ForwardQVisibleAncestorDecoder.visibleList
    Lemma27Repair.visibleAncestors SkewTree.preds
  exact (hTnodup.filter _).filter _

/-- Taking a genuinely typed old source-variable name at a
visible-root index recovers that exact root node. -/
theorem visibleVariable_root_eq_get
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : Fin (ForwardQVisibleAncestorDecoder.visibleList c i).length) :
    (ForwardQVisibleAncestorDecoder.visibleVariable c i z).1.1 =
      (ForwardQVisibleAncestorDecoder.visibleList c i).get z :=
  ForwardQVisibleAncestorDecoder.variableAtSupportRoot_node c _
    (ForwardQVisibleAncestorDecoder.visibleList_get_mem_supportNodes c i z)

/-- Different visible-root indices define different actual
old source-variable subtype elements. -/
theorem visibleVariable_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    Function.Injective
      (ForwardQVisibleAncestorDecoder.visibleVariable c i) := by
  intro z w heq
  have hroots :
      (ForwardQVisibleAncestorDecoder.visibleList c i).get z =
        (ForwardQVisibleAncestorDecoder.visibleList c i).get w := by
    calc
      (ForwardQVisibleAncestorDecoder.visibleList c i).get z =
          (ForwardQVisibleAncestorDecoder.visibleVariable c i z).1.1 :=
        (visibleVariable_root_eq_get c i z).symm
      _ = (ForwardQVisibleAncestorDecoder.visibleVariable c i w).1.1 :=
        congrArg (fun v : c.source.word.Vars => v.1.1) heq
      _ = (ForwardQVisibleAncestorDecoder.visibleList c i).get w :=
        visibleVariable_root_eq_get c i w
  let e := List.Nodup.getEquiv
    (ForwardQVisibleAncestorDecoder.visibleList c i)
    (visibleList_nodup c i)
  apply e.injective
  exact Subtype.ext hroots

/-- Use the duplicate-free visible-root list to assign a
canonical actual finite index to ANY source variable known
to be visible in frontier cone i. -/
noncomputable def indexOfVisibleRoot
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (v : c.source.word.Vars)
    (hv : v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i) :
    Fin (ForwardQVisibleAncestorDecoder.visibleList c i).length :=
  (List.Nodup.getEquiv
    (ForwardQVisibleAncestorDecoder.visibleList c i)
    (visibleList_nodup c i)).symm ⟨v.1.1, hv⟩

/-- The finite visible-root lookup is root-faithful: equality
of indices forces equality of ACTUAL old source variable names. -/
theorem indexOfVisibleRoot_eq_imp_root_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (v w : c.source.word.Vars)
    (hv : v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i)
    (hw : w.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i)
    (heq : indexOfVisibleRoot c i v hv =
      indexOfVisibleRoot c i w hw) :
    v = w := by
  let e := List.Nodup.getEquiv
    (ForwardQVisibleAncestorDecoder.visibleList c i)
    (visibleList_nodup c i)
  have hsub :
      (⟨v.1.1, hv⟩ :
        {r : Node b // r ∈ ForwardQVisibleAncestorDecoder.visibleList c i}) =
      ⟨w.1.1, hw⟩ := e.symm.injective heq
  have hnodes : v.1.1 = w.1.1 := congrArg Subtype.val hsub
  apply Subtype.ext
  apply Subtype.ext
  exact hnodes

/-- Every ACTUAL old source variable root in the visible chain
is represented by one of the canonical finite indices, with
the actual source variable name and not just its root node. -/
theorem visibleVariable_surjective_onto_visible
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (v : c.source.word.Vars)
    (hv : v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i) :
    ∃ z : Fin (ForwardQVisibleAncestorDecoder.visibleList c i).length,
      ForwardQVisibleAncestorDecoder.visibleVariable c i z = v := by
  let e := List.Nodup.getEquiv
    (ForwardQVisibleAncestorDecoder.visibleList c i)
    (visibleList_nodup c i)
  let z := indexOfVisibleRoot c i v hv
  have hget :
      (ForwardQVisibleAncestorDecoder.visibleList c i).get z =
        v.1.1 := by
    have h := e.apply_symm_apply
      (⟨v.1.1, hv⟩ :
        {r : Node b // r ∈ ForwardQVisibleAncestorDecoder.visibleList c i})
    exact congrArg Subtype.val h
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (visibleVariable_root_eq_get c i z).trans hget

/-- The source-facing corrected R_i decoder now reaches EVERY
actual old source VARIABLE in the visible ancestor chain. -/
theorem decodeAux_onto_every_visible_variable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : Index c)
    (v : c.source.word.Vars)
    (hv : v.1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i) :
    ∃ j : Fin (m + 1),
      ForwardQVisibleAncestorDecoder.decodeAux c fallback i j =
        Sum.inr v := by
  obtain ⟨z, hz⟩ :=
    visibleVariable_surjective_onto_visible c i v hv
  have hpos :
      0 < (ForwardQVisibleAncestorDecoder.visibleList c i).length := by
    have h := z.isLt
    omega
  obtain ⟨j, hj⟩ :=
    ForwardQVisibleAncestorDecoder.decodeAux_onto_visible
      c fallback i hpos z
  refine ⟨j, ?_⟩
  simpa [hz] using hj

/-- A cone containing m+2 DISTINCT local variables cannot send
them all INJECTIVELY to the at most m+1 visible old source roots.
This is the exact numerical obstruction to naively retaining all
independent local variable labels in one decoded Q frontier. -/
theorem no_injective_visible_root_transport
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (root : Fin (m + 2) → c.source.word.Vars)
    (hvisible : ∀ z : Fin (m + 2),
      (root z).1.1 ∈ ForwardQVisibleAncestorDecoder.visibleList c i) :
    ¬ Function.Injective root := by
  intro hinj
  let indexMap : Fin (m + 2) →
      Fin (ForwardQVisibleAncestorDecoder.visibleList c i).length :=
    fun z => indexOfVisibleRoot c i (root z) (hvisible z)
  have hindex : Function.Injective indexMap := by
    intro z w heq
    apply hinj
    exact indexOfVisibleRoot_eq_imp_root_eq c i
      (root z) (root w) (hvisible z) (hvisible w) heq
  have hcard :
      m + 2 ≤
        (ForwardQVisibleAncestorDecoder.visibleList c i).length := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective indexMap hindex)
  have hbound := visibleList_length_le c i
  omega

/-- If all m+2 variable symbols actually occur inside one
frontier cone, any genuine locally root-aligned Q decoding
MUST identify at least two of their names. The assumption
that the symbols all occur is essential, and the conclusion
is only a non-injectivity statement, not a counterexample
to the final Ramsey existence theorem. -/
theorem no_injective_coneRoot_of_all_variables_occurring
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (Fin (m + 2)))
    (coneRoot : Index c → Fin (m + 2) → c.source.word.Vars)
    (hocc : ∀ z : Fin (m + 2),
      ∃ t : BoundedNode b n,
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 ∧
        raw i t = Sum.inr z)
    (halign : ∀ (j : Index c) (t : BoundedNode b n)
      (z : Fin (m + 2)),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 t.1 →
      raw j t = Sum.inr z →
      IsPrefix (coneRoot j z).1.1 t.1) :
    ¬ Function.Injective (coneRoot i) := by
  have hvisible : ∀ z : Fin (m + 2),
      (coneRoot i z).1.1 ∈
        ForwardQVisibleAncestorDecoder.visibleList c i := by
    intro z
    obtain ⟨t, ht, hraw⟩ := hocc z
    exact (coneRoot_aligned_iff_visible_at_occurrences
      c raw coneRoot).1 halign i t z ht hraw
  exact no_injective_visible_root_transport c i
    (coneRoot i) hvisible

end DualTree.ForwardQVisibleRootCapacity
