import DualTree.ForwardQSpanExactInjectivity
import DualTree.ForwardQVisibleRootCapacity

/-!
# A sharp numerical local-span capacity theorem for corrected Q cones

The exact evaluated-span preservation criterion only requires
injectivity on genuinely OCCURRING local variable names.

For a fixed corrected forward frontier i, the old source-variable
roots available for a geometrically root-aligned translation
form a duplicate-free visible list V_i.

If q <= |V_i|, one can map Fin q injectively to the FIRST q
actual old variable roots from V_i; the resulting map is
prefix-aligned in the entire full frontier cone and preserves the
FULL evaluated raw local variable span over a two-letter alphabet.

Conversely, if ALL q local names occur in the raw word at
positions inside that frontier cone, any visible-root translation
preserving the full evaluated span must be injective and hence
q <= |V_i|.

This is an exact existence/capacity equivalence for one local
frontier. It is NOT a global mixed-product Ramsey theorem and
does not show that the printed Lemma 27 happens to choose
such q or that its local substitutions fit simultaneously
across all D0 and D2 frontiers.
-/

namespace DualTree.ForwardQVisibleSpanCapacityIff

open ForwardSourceQTree
open ForwardQVisibleAncestorDecoder
open ForwardQVisibleRootCapacity
open ForwardQSpanExactInjectivity

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The first q visible OLD source-variable roots give a literal
typed renaming of q cone variables whenever their number fits
the per-frontier capacity. -/
noncomputable def visibleRootInjection
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hq : q ≤ (visibleList c i).length) :
    Fin q → c.source.word.Vars :=
  fun z => visibleVariable c i (Fin.castLE hq z)

/-- Every selected target is an actual old variable whose root
is a member of the literal visible-source-root list. -/
theorem visibleRootInjection_visible
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hq : q ≤ (visibleList c i).length)
    (z : Fin q) :
    (visibleRootInjection c i hq z).1.1 ∈ visibleList c i := by
  change (visibleVariable c i (Fin.castLE hq z)).1.1 ∈
    visibleList c i
  rw [visibleVariable_root_eq_get c i (Fin.castLE hq z)]
  exact List.get_mem _ _

/-- Consequently each chosen target prefixes EVERY occurrence
in this frontier cone; no arbitrary root-alignment premise is
required. -/
theorem visibleRootInjection_aligned
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hq : q ≤ (visibleList c i).length)
    (z : Fin q)
    (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    IsPrefix (visibleRootInjection c i hq z).1.1 t.1 := by
  have hv := visibleRootInjection_visible c i hq z
  have hp :=
    (ForwardQConeVariableVisibility.sourceRoot_visible_iff_strict_frontier
      c i (visibleRootInjection c i hq z)).1 hv
  exact isPrefix_trans hp.1 ht

/-- The chosen local renaming is injective, because the finite
visible-root list is duplicate-free. -/
theorem visibleRootInjection_injective
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hq : q ≤ (visibleList c i).length) :
    Function.Injective (visibleRootInjection c i hq) := by
  intro u v heq
  change visibleVariable c i (Fin.castLE hq u) =
    visibleVariable c i (Fin.castLE hq v) at heq
  have hindex : Fin.castLE hq u = Fin.castLE hq v :=
    (visibleVariable_injective c i) heq
  exact Fin.ext (congrArg Fin.val hindex)

/-- Every raw local cone word with q variable names preserves
its COMPLETE evaluated span after this root translation when
q fits the actual visible capacity. No occurrence hypothesis
is needed for the positive direction. -/
theorem visibleRootInjection_preserves_span
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hq : q ≤ (visibleList c i).length)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (Fin q))
    (hβ : SpanAudit.HasTwoLetters (Sum α (Fin (m + 1)))) :
    SpanAudit.span
        (SpanAudit.substitute (raw i)
          (fun z => (Sum.inr (visibleRootInjection c i hq z) :
            Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) =
      SpanAudit.span (raw i) := by
  apply (span_eq_iff_injective_on_occurrences
    hβ (raw i) (visibleRootInjection c i hq)).2
  intro u v _ _ heq
  exact visibleRootInjection_injective c i hq heq

/-- If each of q local names ACTUALLY occurs inside a full frontier
cone, a root-aligned, full-span-preserving map into visible old
variables forces q <= |V_i|. -/
theorem capacity_of_visible_span_preserving_root
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (Fin q))
    (hβ : SpanAudit.HasTwoLetters (Sum α (Fin (m + 1))))
    (hocc : ∀ z : Fin q,
      ∃ t : BoundedNode b n,
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 ∧
        raw i t = Sum.inr z)
    (root : Fin q → c.source.word.Vars)
    (hvisible : ∀ z : Fin q, (root z).1.1 ∈ visibleList c i)
    (hspan :
      SpanAudit.span
          (SpanAudit.substitute (raw i)
            (fun z => (Sum.inr (root z) :
              Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) =
        SpanAudit.span (raw i)) :
    q ≤ (visibleList c i).length := by
  have hon :
      InjectiveOnOccurrences (raw i) root :=
    (span_eq_iff_injective_on_occurrences hβ (raw i) root).1 hspan
  have hinj : Function.Injective root := by
    intro z w heq
    obtain ⟨t, _, ht⟩ := hocc z
    obtain ⟨s, _, hs⟩ := hocc w
    exact hon z w ⟨t, ht⟩ ⟨s, hs⟩ heq
  let indexMap : Fin q → Fin (visibleList c i).length :=
    fun z => indexOfVisibleRoot c i (root z) (hvisible z)
  have hind : Function.Injective indexMap := by
    intro z w heq
    apply hinj
    exact indexOfVisibleRoot_eq_imp_root_eq c i
      (root z) (root w) (hvisible z) (hvisible w) heq
  simpa only [Fintype.card_fin] using
    (Fintype.card_le_of_injective indexMap hind)

/-- Exact source-facing numerical criterion for the existence of
a geometrically visible, FULL-local-span-preserving variable
assignment, assuming all q local variable names genuinely occur
inside the cone. -/
theorem exists_visible_span_preserving_root_iff_capacity
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (Fin q))
    (hβ : SpanAudit.HasTwoLetters (Sum α (Fin (m + 1))))
    (hocc : ∀ z : Fin q,
      ∃ t : BoundedNode b n,
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 ∧
        raw i t = Sum.inr z) :
    (∃ root : Fin q → c.source.word.Vars,
      (∀ z : Fin q, (root z).1.1 ∈ visibleList c i) ∧
      SpanAudit.span
          (SpanAudit.substitute (raw i)
            (fun z => (Sum.inr (root z) :
              Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) =
        SpanAudit.span (raw i)) ↔
      q ≤ (visibleList c i).length := by
  constructor
  · rintro ⟨root, hvis, hspan⟩
    exact capacity_of_visible_span_preserving_root
      c i raw hβ hocc root hvis hspan
  · intro hq
    refine ⟨visibleRootInjection c i hq, ?_, ?_⟩
    · exact visibleRootInjection_visible c i hq
    · exact visibleRootInjection_preserves_span c i hq raw hβ

end DualTree.ForwardQVisibleSpanCapacityIff
