import DualTree.ForwardQGlobalHallSpan
import DualTree.ForwardQCanonicalConeRootChoice
import Mathlib.Combinatorics.Hall.Finite

/-!
# Exact Hall condition on ACTUALLY OCCURRING cone variables

The global matching theorem on ALL declared tagged names was a sharp
criterion when every name occurs inside its own corrected Q frontier cone.
This is stronger than needed when local variable words have UNUSED names.

Only occurrences inside their actual complete-support frontier cone
matter for the decoded Q word. First mask all symbols OUTSIDE their
frontier to one fallback constant. Then restrict the tagged local-name
type to those names which really occur in that masked raw word.

A global visible-old-root assignment need only be injective and
visible ON THIS FINITE OCCURRING SUBTYPE; arbitrary unused local
names may be sent to the existing source-cut variable, even if
their corresponding visible-root lists are empty.

Using finite Hall's marriage theorem and the proved evaluated-span
injectivity-on-occurrences criterion, we obtain an EXACT equivalence:
a full independent-coordinate evaluated span is preserved by some
occurrence-aligned old-root assignment iff Hall holds for every set
of ACTUALLY OCCURRING tagged cone-variable names.

Every matched occurrence is automatically root-aligned at its
frontier. This is a precise algebraic/gluing interface, not yet a
proof of the paper's particular g_w or Ramsey recursion.
-/

namespace DualTree.ForwardQOccurringHallSpan

open ForwardSourceQTree
open ForwardQGlobalHallSpan
open ForwardQSpanExactInjectivity

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Remove raw symbols that lie OUTSIDE their own frontier cone.
The true Q selector never uses those symbols, so the masking
changes no relevant local word information. -/
noncomputable def coneRaw
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) :
    ∀ i : Index c, BoundedNode b n → Sum β (Fin (q i)) := by
  classical
  exact fun i t =>
    if IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 then
      raw i t
    else
      Sum.inl fallback

/-- All raw local symbols INSIDE the selected complete frontier
cone remain unchanged. -/
theorem coneRaw_inside
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (i : Index c) (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    coneRaw c q fallback raw i t = raw i t := by
  classical
  simp [coneRaw, ht]

/-- No genuine local variable appears OUTSIDE its own cone in
the masked raw word. -/
theorem coneRaw_outside
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (i : Index c) (t : BoundedNode b n)
    (ht : ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    coneRaw c q fallback raw i t = Sum.inl fallback := by
  classical
  simp [coneRaw, ht]

/-- The genuine variable-occurrence predicate on the TAGGED
disjoint-union word, after masking irrelevant outside-cone input. -/
abbrev OccurringTag
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) :=
  {tag : TaggedVariable c q //
    Occurs (globalRaw c q (coneRaw c q fallback raw)) tag}

/-- Every genuine local raw variable occurrence INSIDE its cone
gives an inhabitant of the ACTUAL occurring tagged-name subtype. -/
theorem occurs_of_raw_inside
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (i : Index c) (z : Fin (q i))
    (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hraw : raw i t = Sum.inr z) :
    Occurs (globalRaw c q (coneRaw c q fallback raw))
      (⟨i,z⟩ : TaggedVariable c q) := by
  refine ⟨⟨i,t⟩, ?_⟩
  simp [globalRaw, coneRaw_inside c q fallback raw i t ht, hraw]

/-- Only the old roots visible above the tagged frontier are
permitted translations of an OCCURRING local variable name. -/
noncomputable def occurringAllowedRoots
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (tag : OccurringTag c q fallback raw) :
    Finset c.source.word.Vars :=
  allowedRoots c q tag.1

/-- Hall's inequalities are required only for genuinely OCCURRING
tagged local names; unused declarations create no demand. -/
def OccurringHall
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) : Prop :=
  ∀ S : Finset (OccurringTag c q fallback raw),
    S.card ≤
      (S.biUnion (occurringAllowedRoots c q fallback raw)).card

/-- Exact finite Hall matching theorem on the occurring tag
subtype of the ACTUAL corrected Q source frame. -/
theorem occurringHall_iff_matching
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) :
    OccurringHall c q fallback raw ↔
      ∃ ρ : OccurringTag c q fallback raw → c.source.word.Vars,
        Function.Injective ρ ∧
        ∀ tag : OccurringTag c q fallback raw,
          ρ tag ∈ occurringAllowedRoots c q fallback raw tag := by
  classical
  exact Finset.all_card_le_biUnion_card_iff_existsInjective'
    (occurringAllowedRoots c q fallback raw)

/-- An injective matching on OCCURRING tags extends to a TOTAL
name map, using the old source-cut variable for unused tags.
Span equality needs injectivity only on the occurring subset. -/
theorem occurringHall_gives_full_span
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (hHall : OccurringHall c q fallback raw) :
    ∃ ρ : TaggedVariable c q → c.source.word.Vars,
      (∀ (tag : TaggedVariable c q)
        (ht : Occurs (globalRaw c q (coneRaw c q fallback raw)) tag),
        ρ tag ∈ allowedRoots c q tag) ∧
      SpanAudit.span
          (SpanAudit.substitute
            (globalRaw c q (coneRaw c q fallback raw))
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span
          (globalRaw c q (coneRaw c q fallback raw)) := by
  classical
  obtain ⟨matching, hinj, hvis⟩ :=
    (occurringHall_iff_matching c q fallback raw).1 hHall
  let w := globalRaw c q (coneRaw c q fallback raw)
  let ρ : TaggedVariable c q → c.source.word.Vars := fun tag =>
    if ht : Occurs w tag then matching ⟨tag,ht⟩
    else ForwardQCanonicalConeRootChoice.cutVariable c
  have hρ :
      ∀ (tag : TaggedVariable c q) (ht : Occurs w tag),
        ρ tag = matching ⟨tag,ht⟩ := by
    intro tag ht
    simp [ρ, ht]
  have hoccInj : InjectiveOnOccurrences w ρ := by
    intro u v hu hv heq
    have hm : matching ⟨u,hu⟩ = matching ⟨v,hv⟩ := by
      calc
        matching ⟨u,hu⟩ = ρ u := (hρ u hu).symm
        _ = ρ v := heq
        _ = matching ⟨v,hv⟩ := hρ v hv
    exact congrArg Subtype.val (hinj hm)
  refine ⟨ρ, ?_, ?_⟩
  · intro tag ht
    rw [hρ tag ht]
    exact hvis ⟨tag,ht⟩
  · exact (span_eq_iff_injective_on_occurrences hβ w ρ).2 hoccInj

/-- Conversely, a total old-root assignment that preserves the
full masked independent-coordinate span and is visible at each
genuine occurrence restricts to an injective Hall matching. -/
theorem occurringHall_of_full_span
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (ρ : TaggedVariable c q → c.source.word.Vars)
    (hvis :
      ∀ (tag : TaggedVariable c q)
        (ht : Occurs (globalRaw c q (coneRaw c q fallback raw)) tag),
        ρ tag ∈ allowedRoots c q tag)
    (hspan :
      SpanAudit.span
          (SpanAudit.substitute
            (globalRaw c q (coneRaw c q fallback raw))
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span
          (globalRaw c q (coneRaw c q fallback raw))) :
    OccurringHall c q fallback raw := by
  let w := globalRaw c q (coneRaw c q fallback raw)
  have hoccInj : InjectiveOnOccurrences w ρ :=
    (span_eq_iff_injective_on_occurrences hβ w ρ).1 hspan
  have hinj :
      Function.Injective
        (fun t : OccurringTag c q fallback raw => ρ t.1) := by
    intro u v heq
    apply Subtype.ext
    exact hoccInj u.1 v.1 u.2 v.2 heq
  exact (occurringHall_iff_matching c q fallback raw).2
    ⟨(fun t => ρ t.1), hinj,
      fun t => hvis t.1 t.2⟩

/-- The EXACT global Hall criterion for preserving all evaluated
assignments of ACTUALLY OCCURRING tagged local cone variables.
Unused names require neither visibility nor injective allocation. -/
theorem full_span_preserving_root_iff_occurringHall
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β) :
    (∃ ρ : TaggedVariable c q → c.source.word.Vars,
      (∀ (tag : TaggedVariable c q)
        (ht : Occurs (globalRaw c q (coneRaw c q fallback raw)) tag),
        ρ tag ∈ allowedRoots c q tag) ∧
      SpanAudit.span
          (SpanAudit.substitute
            (globalRaw c q (coneRaw c q fallback raw))
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span
          (globalRaw c q (coneRaw c q fallback raw))) ↔
      OccurringHall c q fallback raw := by
  constructor
  · rintro ⟨ρ, hvis, hspan⟩
    exact occurringHall_of_full_span c q fallback raw hβ ρ hvis hspan
  · intro hHall
    exact occurringHall_gives_full_span c q fallback raw hβ hHall

/-- The selected translated old root genuinely precedes its
frontier at each ACTUAL local variable occurrence, as required
for a legal three-way decoded source word. -/
theorem occurringHall_gives_prefix_alignment
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (hHall : OccurringHall c q fallback raw) :
    ∃ ρ : TaggedVariable c q → c.source.word.Vars,
      (SpanAudit.span
          (SpanAudit.substitute
            (globalRaw c q (coneRaw c q fallback raw))
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span
          (globalRaw c q (coneRaw c q fallback raw))) ∧
      (∀ (i : Index c) (z : Fin (q i))
        (t : BoundedNode b n),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
        raw i t = Sum.inr z →
        IsPrefix (ρ ⟨i,z⟩).1.1 t.1) := by
  obtain ⟨ρ, hvis, hspan⟩ :=
    occurringHall_gives_full_span c q fallback raw hβ hHall
  refine ⟨ρ, hspan, ?_⟩
  intro i z t ht hraw
  have hocc : Occurs
      (globalRaw c q (coneRaw c q fallback raw))
      (⟨i,z⟩ : TaggedVariable c q) :=
    occurs_of_raw_inside c q fallback raw i z t ht hraw
  exact matched_root_prefixes_cone c q
    (⟨i,z⟩ : TaggedVariable c q) (ρ ⟨i,z⟩)
    (hvis _ hocc) t ht

end DualTree.ForwardQOccurringHallSpan
