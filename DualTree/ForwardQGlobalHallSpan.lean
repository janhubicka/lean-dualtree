import DualTree.ForwardQVisibleSpanCapacityIff
import DualTree.ForwardQSpanExactInjectivity
import Mathlib.Combinatorics.Hall.Finite

/-!
# Global Hall allocation for independent corrected Q-frontier variables

Local frontier capacities q_i <= |V_i| are NOT sufficient to preserve
independent variables across multiple D0/D2 cones: the visible old
source-root lists V_i may overlap.

Tag every local variable by its ACTUAL forward-sorted frontier index i.
The resulting finite Sigma type records independent local names, even
when two local component words both call one of their names 'z'.

Each tagged variable (i,z) is allowed to map only to genuine old source
variables whose roots belong to V_i. Hall's marriage theorem gives the
exact criterion for a globally injective visible-root assignment:
  |E'| <= | union_{(i,z) in E'} V_i |
for EVERY finite subset E' of the tagged names, not just whole cones.

Injectivity of this global assignment preserves the evaluated span of
the disjoint-union raw local words. Conversely if every tagged name
actually occurs inside its own cone and the alphabet has two distinct
letters, full evaluated-span preservation implies an injective
assignment and hence ALL Hall inequalities.

This is a sharp algebraic/finite matching interface on an actual
corrected Q frame; it is not a proof that the particular cone words of
Lemma 27 satisfy Hall's inequalities, that the associated local
substitutions define the printed g_w, or that the Ramsey recursion works.
-/

namespace DualTree.ForwardQGlobalHallSpan

open ForwardSourceQTree
open ForwardQVisibleAncestorDecoder
open ForwardQVisibleRootCapacity
open ForwardQSpanExactInjectivity

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Tagged local variables retain their genuine frontier index.
The number q i of local names can vary from cone to cone. -/
abbrev TaggedVariable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat) :=
  Σ i : Index c, Fin (q i)

/-- The finite set of ACTUAL old source-variable subtype elements
allowed as translations of a tagged variable (i,z). -/
noncomputable def allowedRoots
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (tag : TaggedVariable c q) : Finset c.source.word.Vars := by
  classical
  exact (Finset.univ :
      Finset (Fin (visibleList c tag.1).length)).image
    (visibleVariable c tag.1)

/-- A target belongs to the allowed set if and only if its
literal root occurs in the checked visible-source-root list. -/
theorem mem_allowedRoots_iff_visible
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (tag : TaggedVariable c q)
    (v : c.source.word.Vars) :
    v ∈ allowedRoots c q tag ↔ v.1.1 ∈ visibleList c tag.1 := by
  classical
  constructor
  · intro hv
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hv
    have hget := visibleVariable_root_eq_get c tag.1 z
    rw [← hz, hget]
    exact List.get_mem _ _
  · intro hv
    obtain ⟨z, hz⟩ :=
      visibleVariable_surjective_onto_visible c tag.1 v hv
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩

/-- Hall's full family of inequalities for all collections of
tagged independent local cone-variable names. -/
def HallCondition
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat) : Prop :=
  ∀ S : Finset (TaggedVariable c q),
    S.card ≤ (S.biUnion (allowedRoots c q)).card

/-- Exact global matching theorem specialized to the ACTUAL
finite visible source-root families of the corrected Q frame. -/
theorem hall_iff_injective_visible_matching
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat) :
    HallCondition c q ↔
      ∃ ρ : TaggedVariable c q → c.source.word.Vars,
        Function.Injective ρ ∧
        ∀ tag : TaggedVariable c q, ρ tag ∈ allowedRoots c q tag := by
  classical
  exact Finset.all_card_le_biUnion_card_iff_existsInjective'
    (allowedRoots c q)

/-- Every matching target is an old root STRICTLY preceding
the assigned frontier, so it prefixes every point in that cone. -/
theorem matched_root_prefixes_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (tag : TaggedVariable c q)
    (v : c.source.word.Vars)
    (hv : v ∈ allowedRoots c q tag)
    (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut tag.1).1 t.1) :
    IsPrefix v.1.1 t.1 := by
  have hvisible :=
    (mem_allowedRoots_iff_visible c q tag v).1 hv
  have hstrict :=
    (ForwardQConeVariableVisibility.sourceRoot_visible_iff_strict_frontier
      c tag.1 v).1 hvisible
  exact isPrefix_trans hstrict.1 ht

/-- The union of all coordinate word domains is used only to
model INDEPENDENT local substitutions, not as a claim that
these different cone words already form one source Q word. -/
def globalRaw
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) :
    (Σ i : Index c, BoundedNode b n) →
      Sum β (TaggedVariable c q)
  | ⟨i, t⟩ =>
      match raw i t with
      | Sum.inl a => Sum.inl a
      | Sum.inr z => Sum.inr ⟨i, z⟩

/-- Each declared local variable name genuinely occurs inside
its own full frontier cone; this is needed for the converse
from full-span preservation to injectivity on ALL tags. -/
def EveryTagOccursInCone
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) : Prop :=
  ∀ (i : Index c) (z : Fin (q i)),
    ∃ t : BoundedNode b n,
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 ∧
      raw i t = Sum.inr z

/-- Every declared tagged variable is a genuine variable
of the disjoint-union raw family under the occurrence assumption. -/
theorem every_tag_occurs_globalRaw
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hocc : EveryTagOccursInCone c q raw)
    (tag : TaggedVariable c q) :
    Occurs (globalRaw c q raw) tag := by
  rcases tag with ⟨i, z⟩
  obtain ⟨t, _, hraw⟩ := hocc i z
  refine ⟨⟨i, t⟩, ?_⟩
  simp [globalRaw, hraw]

/-- The global Hall condition produces a root-aligned, injective
name translation from ALL tagged independent local variables. -/
theorem hall_gives_root_aligned_matching
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (hHall : HallCondition c q) :
    ∃ ρ : TaggedVariable c q → c.source.word.Vars,
      Function.Injective ρ ∧
      (∀ tag : TaggedVariable c q, ρ tag ∈ allowedRoots c q tag) ∧
      (∀ (tag : TaggedVariable c q) (t : BoundedNode b n),
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut tag.1).1 t.1 →
        IsPrefix (ρ tag).1.1 t.1) := by
  obtain ⟨ρ, hinj, hvis⟩ :=
    (hall_iff_injective_visible_matching c q).1 hHall
  exact ⟨ρ, hinj, hvis,
    fun tag t ht =>
      matched_root_prefixes_cone c q tag (ρ tag) (hvis tag) t ht⟩

/-- A globally injective name matching preserves the ENTIRE
independent tagged evaluated span (a disjoint union of raw
cone-coordinate positions). Positivity requires no occurrence
hypothesis; each tag may be unused. -/
theorem global_span_preserved_of_injective
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (ρ : TaggedVariable c q → c.source.word.Vars)
    (hinj : Function.Injective ρ) :
    SpanAudit.span
        (SpanAudit.substitute (globalRaw c q raw)
          (fun tag => (Sum.inr (ρ tag) :
            Sum β c.source.word.Vars))) =
      SpanAudit.span (globalRaw c q raw) := by
  apply (span_eq_iff_injective_on_occurrences
    hβ (globalRaw c q raw) ρ).2
  intro u v _ _ heq
  exact hinj heq

/-- A globally full-span-preserving VISIBLE root allocation of
genuinely occurring names is necessarily injective, hence
forces the full Hall condition for ALL subsets of the tags. -/
theorem hall_of_full_global_span
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (hocc : EveryTagOccursInCone c q raw)
    (ρ : TaggedVariable c q → c.source.word.Vars)
    (hvisible : ∀ tag : TaggedVariable c q,
      ρ tag ∈ allowedRoots c q tag)
    (hspan :
      SpanAudit.span
          (SpanAudit.substitute (globalRaw c q raw)
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span (globalRaw c q raw)) :
    HallCondition c q := by
  have hinjOcc : InjectiveOnOccurrences (globalRaw c q raw) ρ :=
    (span_eq_iff_injective_on_occurrences
      hβ (globalRaw c q raw) ρ).1 hspan
  have hinj : Function.Injective ρ := by
    intro u v huv
    exact hinjOcc u v
      (every_tag_occurs_globalRaw c q raw hocc u)
      (every_tag_occurs_globalRaw c q raw hocc v) huv
  exact (hall_iff_injective_visible_matching c q).2
    ⟨ρ, hinj, hvisible⟩

/-- Sharp GLOBAL matching/spanning criterion for the genuine
visible-old-root families. Local inequalities q_i <= |V_i|
alone do not imply this condition; Hall must hold on EVERY
subset of INDEPENDENT tagged names. -/
theorem exists_full_global_span_iff_hall
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hβ : SpanAudit.HasTwoLetters β)
    (hocc : EveryTagOccursInCone c q raw) :
    (∃ ρ : TaggedVariable c q → c.source.word.Vars,
      (∀ tag, ρ tag ∈ allowedRoots c q tag) ∧
      SpanAudit.span
          (SpanAudit.substitute (globalRaw c q raw)
            (fun tag => (Sum.inr (ρ tag) :
              Sum β c.source.word.Vars))) =
        SpanAudit.span (globalRaw c q raw)) ↔
      HallCondition c q := by
  constructor
  · rintro ⟨ρ, hvis, hspan⟩
    exact hall_of_full_global_span c q raw hβ hocc
      ρ hvis hspan
  · intro hHall
    obtain ⟨ρ, hinj, hvis⟩ :=
      (hall_iff_injective_visible_matching c q).1 hHall
    refine ⟨ρ, hvis, ?_⟩
    exact global_span_preserved_of_injective c q raw hβ ρ hinj

end DualTree.ForwardQGlobalHallSpan
