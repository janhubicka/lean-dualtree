import DualTree.ForwardQHallConeData
import DualTree.ForwardQSpanExactInjectivity

/-!
# Simultaneous evaluations for Hall-allocated Q-cone variables

PR #255 constructs one legal corrected Q starred word from an occurrence-level
Hall matching, and proves equality of the abstract *tagged* evaluated spans.
Here we extract the stronger source-facing quantifier order needed by the
Ramsey application: ONE Q word works for EVERY simultaneous assignment to
the genuinely occurring independent local cone variables. For each assignment
there is ONE assignment to the old source-variable roots that realizes it,
pointwise, at EVERY such occurrence inside the actual sorted D0/D2 cones.

We also record the necessary absolute capacity bound on the old source
variable type. This matters because the Hall premise is not automatic from
individual cone capacities, and can fail when too many independent local
variables are present.

These statements remain conditional on Hall for the local raw words. They
do not identify the words with the specific g_w of Lemma 27, control the
outside-cone old-source letters under the chosen evaluation, or establish
Definition 24 simplicity or the Ramsey recursion.
-/

namespace DualTree.ForwardQHallEvaluations

open ForwardSourceQTree
open ForwardQGlobalHallSpan
open ForwardQOccurringHallSpan
open ForwardQSpanExactInjectivity

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Cardinality of the finite subtype of actually occurring tagged
names. The occurrence predicate is not computably decidable, so we
make its finite instance explicitly classical at definition time. -/
noncomputable def occurringCount
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i))) : Nat := by
  classical
  exact Fintype.card (OccurringTag c q fallback raw)

/-- A root map injective on the variables that ACTUALLY occur admits
a simultaneous extension of every assignment of source names.
There is no requirement to distinguish unused variables. -/
theorem extend_occurring_assignment
    {ι κ ν β α : Type*}
    (w : ι → Sum β κ)
    (ρ : κ → ν)
    (hinj : InjectiveOnOccurrences w ρ)
    (fallback : α)
    (σ : κ → α) :
    ∃ τ : ν → α,
      ∀ v : κ, Occurs w v → τ (ρ v) = σ v := by
  classical
  let τ : ν → α := fun u =>
    if h : ∃ v : κ, Occurs w v ∧ ρ v = u then
      σ (Classical.choose h)
    else fallback
  refine ⟨τ, ?_⟩
  intro v hv
  have hsome : ∃ v' : κ, Occurs w v' ∧ ρ v' = ρ v :=
    ⟨v, hv, rfl⟩
  have hh : Occurs w (Classical.choose hsome) ∧
      ρ (Classical.choose hsome) = ρ v :=
    Classical.choose_spec hsome
  have hchoice : Classical.choose hsome = v :=
    hinj _ _ hh.1 hv hh.2
  simp [τ, hsome, hchoice]

/-- The WHOLE collection of genuinely occurring tagged variables
cannot be larger than the available old source-variable type.
Unlike the per-frontier bounds, this is a global obstruction. -/
theorem occurringHall_total_capacity
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hHall : OccurringHall c q fallback raw) :
    occurringCount c q fallback raw ≤
      Fintype.card c.source.word.Vars := by
  classical
  have hHallAll :=
    hHall (Finset.univ : Finset (OccurringTag c q fallback raw))
  have hsubset :
      (Finset.univ : Finset (OccurringTag c q fallback raw)).biUnion
        (occurringAllowedRoots c q fallback raw) ⊆
          (Finset.univ : Finset c.source.word.Vars) :=
    Finset.subset_univ _
  have hle := hHallAll.trans (Finset.card_le_card hsubset)
  simpa [occurringCount] using hle

/-- More genuinely independent local variable names than old
source roots make the occurrence-level Hall criterion impossible. -/
theorem not_occurringHall_of_excess
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (q : Index c → Nat)
    (fallback : β)
    (raw : ∀ i : Index c,
      BoundedNode b n → Sum β (Fin (q i)))
    (hexcess :
      Fintype.card c.source.word.Vars <
        occurringCount c q fallback raw) :
    ¬ OccurringHall c q fallback raw := by
  intro hHall
  exact (Nat.not_lt_of_ge
    (occurringHall_total_capacity c q fallback raw hHall)) hexcess

/-- One Hall-constructed ACTUAL corrected Q word realizes, through
one evaluation of its genuine old source roots, EVERY simultaneous
assignment to all independently tagged occurring cone variables.

This is a concrete pointwise evaluation theorem at the original
three-constructor positions, not merely equality of two abstract
sets of evaluated tagged words. The auxiliary positions retain
their own R_i decoding, but no independence statement about
the auxiliary values or the unchanged outside-cone word is made.
-/
theorem hall_Q_realizes_all_local_variable_assignments
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
    (hHall : OccurringHall c q (Sum.inl fallback) raw) :
    ∃ d : ForwardQFullFrontierThreeWay.ConeData c
        (Fin (m + 1)) (TaggedVariable c q),
      (d.onActualStarredQ hb c x hTbound).tree =
        (nodes c x.1).toList ∧
      ∀ σ : TaggedVariable c q → α,
        ∃ τ : c.source.word.Vars → α,
          ∀ (i : Index c) (t : BoundedNode b n)
            (z : Fin (q i)),
            IsPrefix
              (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
            raw i t = Sum.inr z →
            SpanAudit.evalSymbol τ
              ((d.onActualStarredQ hb c x hTbound).word.word t) =
                σ ⟨i,z⟩ := by
  classical
  obtain ⟨ρ, d, hinside, hroot, hspan⟩ :=
    ForwardQHallConeData.hall_constructs_coneData_and_span
      c q fallback raw hHall
  let w := globalRaw c q
    (coneRaw c q (Sum.inl fallback) raw)
  have hinj : InjectiveOnOccurrences w ρ :=
    (span_eq_iff_injective_on_occurrences
      (ForwardQHallConeData.enlargedAlphabet_two_letters fallback)
      w ρ).1 hspan
  refine ⟨d, d.onActualStarredQ_tree hb c x hTbound, ?_⟩
  intro σ
  obtain ⟨τ, hτ⟩ :=
    extend_occurring_assignment w ρ hinj fallback σ
  refine ⟨τ, ?_⟩
  intro i t z ht hraw
  have htag :
      ForwardQHallConeData.taggedConeRaw c q fallback raw i t =
        Sum.inr (⟨i,z⟩ : TaggedVariable c q) := by
    rw [ForwardQHallConeData.taggedConeRaw_inside
      c q fallback raw i t ht, hraw]
  have hdtag :
      d.raw i t = Sum.inr (⟨i,z⟩ : TaggedVariable c q) :=
    (hinside i t ht).trans htag
  have hsymbol :
      d.localSymbol i t = Sum.inr (ρ ⟨i,z⟩) := by
    have hword :=
      ConeWordLift.liftWord_variable
        (d.raw i) (d.decodeAux i) (d.coneRoot i)
        t ⟨i,z⟩ hdtag
    change d.localSymbol i t =
      Sum.inr (d.coneRoot i ⟨i,z⟩) at hword
    rw [hword, hroot i ⟨i,z⟩]
  have hvalue :
      SpanAudit.evalSymbol τ
        ((d.onActualStarredQ hb c x hTbound).word.word t) =
          τ (ρ ⟨i,z⟩) := by
    rw [d.symbol_inside hb c x hTbound i t ht, hsymbol]
    rfl
  exact hvalue.trans
    (hτ ⟨i,z⟩
      (occurs_of_raw_inside
        c q (Sum.inl fallback) raw i z t ht hraw))

end DualTree.ForwardQHallEvaluations
