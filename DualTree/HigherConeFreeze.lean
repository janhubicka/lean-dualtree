import DualTree.HigherConeAddresses

/-!
# Track C: exact evaluation with selected and frozen Hales--Jewett cones

We must not replace unused cone words by a constant *wholesale*:
an HJ word's genuine fixed letters must be retained. Instead, we freeze only
the variable occurrences at unused addresses, leaving its fixed letters
unchanged. The selected b cone addresses receive b independent variable
names.

These lemmas prove the needed flat evaluation algebra, not yet the
tree-indexed k=2 word legality or the Ramsey pullback.
-/

namespace DualTree.HigherConeFreeze

open HigherConeAddresses

/-- The unique parameter value at each selected branch, with every other
address set to fallback. Distinctness is certified by branchAddress_injective. -/
noncomputable def freezeAssignment
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (σ : Fin d → Fin b → β) :
    Fin d → Address b N → β := by
  classical
  exact fun coord a =>
    if h : ∃ dir : Fin b, branchAddress hb r dir = a
    then σ coord (Classical.choose h)
    else fallback

/-- Freeze does not alter any selected branch parameter. -/
theorem freezeAssignment_selected
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (σ : Fin d → Fin b → β) (coord : Fin d) (dir : Fin b) :
    freezeAssignment hb r fallback σ coord (branchAddress hb r dir) =
      σ coord dir := by
  classical
  change (if h : ∃ j : Fin b, branchAddress hb r j = branchAddress hb r dir
    then σ coord (Classical.choose h) else fallback) = σ coord dir
  split_ifs with h
  · have hchosen : branchAddress hb r (Classical.choose h) =
        branchAddress hb r dir := Classical.choose_spec h
    have heq : Classical.choose h = dir :=
      (branchAddress_injective hb r) hchosen
    simpa [heq]
  · exact (h ⟨dir, rfl⟩).elim

/-- A selected cone has a distinct variable name for every outgoing
direction; fixed letters remain those of the full product-alphabet word. -/
def selectedConeSymbol
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (selected : Fin b → Address b N)
    (coord : Fin d)
    (position : Fin b × Fin M) : Sum β (Fin b) :=
  match w position.2 with
  | Sum.inl letters => Sum.inl (letters coord (selected position.1))
  | Sum.inr _ => Sum.inr position.1

/-- Every selected direction is an ACTUALLY OCCURRING variable if the
cone word is proper. -/
theorem selectedConeSymbol_occurs
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (selected : Fin b → Address b N) (coord : Fin d)
    (hproper : ∀ v : Fin 1, ∃ j : Fin M, w j = Sum.inr v)
    (dir : Fin b) :
    ∃ position : Fin b × Fin M,
      selectedConeSymbol w selected coord position = Sum.inr dir := by
  obtain ⟨j, hj⟩ := hproper 0
  exact ⟨(dir, j), by simp [selectedConeSymbol, hj]⟩

/-- The selected b-parameter word evaluates *exactly* as the original
product-alphabet HJ cone word evaluated under the frozen assignment.
No diagonal restriction of direction variables is introduced. -/
theorem selectedConeSymbol_eval
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (σ : Fin d → Fin b → β)
    (coord : Fin d) (dir : Fin b) (j : Fin M) :
    SpanAudit.eval
        (selectedConeSymbol w (branchAddress hb r) coord)
        (σ coord) (dir, j) =
      ((SpanAudit.eval w
          (fun _ : Fin 1 => freezeAssignment hb r fallback σ) j) coord)
        (branchAddress hb r dir) := by
  cases hw : w j with
  | inl letters =>
      simp [SpanAudit.eval, SpanAudit.evalSymbol, selectedConeSymbol, hw]
  | inr v =>
      simpa [SpanAudit.eval, SpanAudit.evalSymbol, selectedConeSymbol, hw]
        using (freezeAssignment_selected hb r fallback σ coord dir).symm

/-- What an UNUSED cone must retain: all existing HJ constants and a
fallback letter only for the positions containing the cone variable. -/
def frozenConeValue
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (fallback : β) (coord : Fin d) (address : Address b N)
    (j : Fin M) : β :=
  match w j with
  | Sum.inl letters => letters coord address
  | Sum.inr _ => fallback

theorem frozenConeValue_fixed
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (fallback : β) (coord : Fin d) (address : Address b N)
    (j : Fin M) (letters : Fin d → Address b N → β)
    (h : w j = Sum.inl letters) :
    frozenConeValue w fallback coord address j = letters coord address := by
  simp [frozenConeValue, h]

theorem frozenConeValue_variable
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (fallback : β) (coord : Fin d) (address : Address b N)
    (j : Fin M) (v : Fin 1)
    (h : w j = Sum.inr v) :
    frozenConeValue w fallback coord address j = fallback := by
  simp [frozenConeValue, h]

/-- The selected b-variable flat span is genuinely inhabited for every
supplied alphabet letter. The true k=2 tree embedding remains separate. -/
theorem selectedConeSymbol_span_nonempty
    {b N M d : Nat} {β : Type*}
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (selected : Fin b → Address b N) (coord : Fin d)
    (fallback : β) :
    (SpanAudit.span (selectedConeSymbol w selected coord)).Nonempty := by
  refine ⟨SpanAudit.eval (selectedConeSymbol w selected coord)
    (fun _ => fallback), ?_⟩
  exact ⟨fun _ => fallback, rfl⟩

end DualTree.HigherConeFreeze
