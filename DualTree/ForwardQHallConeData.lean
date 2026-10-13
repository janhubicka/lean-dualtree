import DualTree.ForwardQOccurringHallSpan
import DualTree.ForwardQVisibleAncestorDecoder
import DualTree.ForwardQFullFrontierThreeWay

/-!
# Turn a GLOBAL Hall matching into an actual full-frontier Q word

The checked occurrence-level Hall theorem provides a total assignment
from independent tagged cone variables to genuine old source variables.
At all genuinely occurring local names the assigned root belongs to
the visible old-root list of the corresponding frontier.

This module assembles those independent local cone words into the
verified three-constructor ConeData interface: original letters,
auxiliary letters decoded by the ACTUAL visible-ancestor R_i, and
genuine local variables tagged with their frontier.

The original raw words are used inside every complete-support
frontier cone (D0 and D2); symbols outside the cone are masked.
Hall visibility discharges the root-prefix alignment of genuine
cone variables, so no arbitrary coneRoot alignment premise remains.
The resulting decoded starred Q word has the actual corrected
support, and its pointwise symbol/evaluation equations hold.

The Hall assignment also preserves the evaluated span of the
disjoint union of independent local cone words. This is CONDITIONAL
on Hall for the particular raw local family. It does not identify
that family with Lemma 27's printed g_w, transport Definition 24's
B1/B2 simplicity condition, or finish the Ramsey recursion.
-/

namespace DualTree.ForwardQHallConeData

open ForwardSourceQTree
open ForwardQGlobalHallSpan
open ForwardQOccurringHallSpan

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The enlarged local alphabet automatically contains two
distinct constructors, even if the original alphabet has
only one letter: an old letter and one auxiliary label. -/
theorem enlargedAlphabet_two_letters
    {m : Nat} {α : Type*}
    (fallback : α) :
    SpanAudit.HasTwoLetters (Sum α (Fin (m + 1))) := by
  refine ⟨Sum.inl fallback, Sum.inr ⟨0, by omega⟩, ?_⟩
  intro h
  cases h

/-- The raw word for the verified three-way Q decoder. Genuine
cone variables have the globally independent TAGGED type,
rather than identifying equally named local variables of
different corrected frontier coordinates. -/
noncomputable def taggedConeRaw
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : α)
    (raw : ∀ i : Index c,
      BoundedNode b n →
        Sum (Sum α (Fin (m + 1))) (Fin (q i))) :
    Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (TaggedVariable c q) :=
  fun i t =>
    match ForwardQOccurringHallSpan.coneRaw c q
      (Sum.inl fallback) raw i t with
    | Sum.inl a => Sum.inl a
    | Sum.inr z => Sum.inr ⟨i,z⟩

/-- All original raw local symbols are retained inside their
actual complete-support frontier cones, without weakening
the three-constructor distinctions. -/
theorem taggedConeRaw_inside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : α)
    (raw : ∀ i : Index c,
      BoundedNode b n →
        Sum (Sum α (Fin (m + 1))) (Fin (q i)))
    (i : Index c) (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    taggedConeRaw c q fallback raw i t =
      match raw i t with
      | Sum.inl a => Sum.inl a
      | Sum.inr z => Sum.inr (⟨i,z⟩ : TaggedVariable c q) := by
  simp [taggedConeRaw,
    ForwardQOccurringHallSpan.coneRaw_inside c q
      (Sum.inl fallback) raw i t ht]

/-- Any local symbol outside its OWN full frontier cone is
ignored; that raw position is replaced by a fallback old letter. -/
theorem taggedConeRaw_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : α)
    (raw : ∀ i : Index c,
      BoundedNode b n →
        Sum (Sum α (Fin (m + 1))) (Fin (q i)))
    (i : Index c) (t : BoundedNode b n)
    (ht : ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    taggedConeRaw c q fallback raw i t =
      Sum.inl (Sum.inl fallback) := by
  simp [taggedConeRaw,
    ForwardQOccurringHallSpan.coneRaw_outside c q
      (Sum.inl fallback) raw i t ht]

/-- Hall's inequalities on ACTUALLY occurring independent local
variables build a legal three-way ConeData and a total root
assignment. No extra genuine-variable alignment hypothesis is
required: the visible matching supplies it automatically. -/
theorem hall_constructs_coneData_and_span
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : α)
    (raw : ∀ i : Index c,
      BoundedNode b n →
        Sum (Sum α (Fin (m + 1))) (Fin (q i)))
    (hHall : ForwardQOccurringHallSpan.OccurringHall c q
      (Sum.inl fallback) raw) :
    ∃ (ρ : TaggedVariable c q → c.source.word.Vars)
      (d : ForwardQFullFrontierThreeWay.ConeData c
        (Fin (m + 1)) (TaggedVariable c q)),
      (∀ (i : Index c) (t : BoundedNode b n),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        d.raw i t = taggedConeRaw c q fallback raw i t) ∧
      (∀ (i : Index c) (tag : TaggedVariable c q),
        d.coneRoot i tag = ρ tag) ∧
      SpanAudit.span
          (SpanAudit.substitute
            (globalRaw c q (ForwardQOccurringHallSpan.coneRaw c q
              (Sum.inl fallback) raw))
            (fun tag => (Sum.inr (ρ tag) :
              Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) =
        SpanAudit.span
          (globalRaw c q (ForwardQOccurringHallSpan.coneRaw c q
            (Sum.inl fallback) raw)) := by
  classical
  obtain ⟨ρ, hvis, hspan⟩ :=
    ForwardQOccurringHallSpan.occurringHall_gives_full_span
      c q (Sum.inl fallback) raw
      (enlargedAlphabet_two_letters fallback) hHall
  have halign :
      ∀ (i : Index c) (t : BoundedNode b n)
        (tag : TaggedVariable c q),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        taggedConeRaw c q fallback raw i t = Sum.inr tag →
        IsPrefix (ρ tag).1.1 t.1 := by
    intro i t tag ht htag
    cases hlocal :
        ForwardQOccurringHallSpan.coneRaw c q
          (Sum.inl fallback) raw i t with
    | inl a =>
        simp [taggedConeRaw, hlocal] at htag
    | inr z =>
        have htagEq :
            (⟨i,z⟩ : TaggedVariable c q) = tag := by
          simpa [taggedConeRaw, hlocal] using htag
        subst tag
        have hocc : ForwardQSpanExactInjectivity.Occurs
            (globalRaw c q (ForwardQOccurringHallSpan.coneRaw
              c q (Sum.inl fallback) raw))
            (⟨i,z⟩ : TaggedVariable c q) := by
          refine ⟨⟨i,t⟩, ?_⟩
          simp [globalRaw, hlocal]
        exact matched_root_prefixes_cone c q
          (⟨i,z⟩ : TaggedVariable c q) (ρ ⟨i,z⟩)
          (hvis _ hocc) t ht
  let d : ForwardQFullFrontierThreeWay.ConeData c
      (Fin (m + 1)) (TaggedVariable c q) :=
    ForwardQVisibleAncestorDecoder.coneData c fallback
      (taggedConeRaw c q fallback raw)
      (fun _ tag => ρ tag) halign
  refine ⟨ρ,d,?_,?_,hspan⟩
  · intro i t ht
    exact ForwardQVisibleAncestorDecoder.coneData_raw_inside
      c fallback (taggedConeRaw c q fallback raw)
      (fun _ tag => ρ tag) halign i t ht
  · intro i tag
    rfl

/-- A Hall matching for the actual corrected Q input frame
therefore yields a LEGAL starred Q word on the exact
reconstructed support, with concrete auxiliary R_i and
globally tagged old-root translations. -/
theorem hall_constructs_actual_starred_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (q : Index c → Nat)
    (fallback : α)
    (raw : ∀ i : Index c,
      BoundedNode b n →
        Sum (Sum α (Fin (m + 1))) (Fin (q i)))
    (hHall : ForwardQOccurringHallSpan.OccurringHall c q
      (Sum.inl fallback) raw) :
    ∃ d : ForwardQFullFrontierThreeWay.ConeData c
        (Fin (m + 1)) (TaggedVariable c q),
      (d.onActualStarredQ hb c x hTbound).tree =
        (nodes c x.1).toList ∧
      (∀ (i : Index c) (t : BoundedNode b n),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        (d.onActualStarredQ hb c x hTbound).word.word t =
          d.localSymbol i t) := by
  obtain ⟨ρ,d,_,_,_⟩ :=
    hall_constructs_coneData_and_span c q fallback raw hHall
  refine ⟨d, ?_, ?_⟩
  · exact d.onActualStarredQ_tree hb c x hTbound
  · intro i t ht
    exact d.symbol_inside hb c x hTbound i t ht

end DualTree.ForwardQHallConeData
