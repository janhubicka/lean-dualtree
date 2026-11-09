import DualTree.HigherConeFreeze

/-!
# Track C: root/cone rectangular colorings with exact frozen addresses

This module converts the flat Hales--Jewett cone variable into a genuine
family of b independent selected branch parameters. Every unused address
retains the fixed Hales--Jewett letters, and only variable positions are
frozen to the specified fallback. The monochromaticity conclusion remains
over the FULL depth-N address matrix. This is a proved finite-coloring
input, not a complete-skew tree word or the k=2 Ramsey theorem.
-/

namespace DualTree.HigherConeRectangular

open HigherConeAddresses
open HigherConeFreeze

/-- Evaluate the original product-alphabet cone word at an assignment which
has independent values on each selected direction and a constant fallback
on all unused addresses. -/
noncomputable def coneEvaluation
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (τ : Fin d → Fin b → β) :
    Fin M → Fin d → Address b N → β :=
  SpanAudit.eval w (fun _ : Fin 1 => freezeAssignment hb r fallback τ)

/-- The full product-alphabet evaluation restricted to a chosen direction
is exactly the evaluation of that direction's independent-variable word. -/
theorem coneEvaluation_selected
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (τ : Fin d → Fin b → β)
    (coord : Fin d) (dir : Fin b) (j : Fin M) :
    coneEvaluation hb r fallback w τ j coord (branchAddress hb r dir) =
      SpanAudit.eval
        (selectedConeSymbol w (branchAddress hb r) coord)
        (τ coord) (dir, j) := by
  exact (selectedConeSymbol_eval hb r fallback w τ coord dir j).symm

/-- Outside the selected branches, fixed cone letters survive literally;
only Hales--Jewett variable occurrences are replaced by the fallback. -/
theorem coneEvaluation_unselected
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (r : Fin N) (fallback : β)
    (w : Fin M → Sum (Fin d → Address b N → β) (Fin 1))
    (τ : Fin d → Fin b → β)
    (coord : Fin d) (a : Address b N) (j : Fin M)
    (ha : ∀ dir : Fin b, branchAddress hb r dir ≠ a) :
    coneEvaluation hb r fallback w τ j coord a =
      frozenConeValue w fallback coord a j := by
  classical
  have hnone : ¬ ∃ dir : Fin b, branchAddress hb r dir = a := by
    rintro ⟨dir, hdir⟩
    exact ha dir hdir
  cases hw : w j with
  | inl letters =>
      simp [coneEvaluation, SpanAudit.eval, SpanAudit.evalSymbol,
        frozenConeValue, hw]
  | inr v =>
      simp [coneEvaluation, SpanAudit.eval, SpanAudit.evalSymbol,
        freezeAssignment, frozenConeValue, hw, hnone]

/-- For every finite coloring we obtain a root Hales--Jewett word and an
actual root position r where its variable occurs, along with a proper cone
word whose b selected branches can be assigned independently. The color
is uniform for every combination of root values and branch values. -/
theorem exists_monochromatic_root_and_selected_cones
    (b : Nat) (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (d : Nat) (fallback : β) :
    ∃ N M : Nat,
      ∀ C : (Fin N → Fin d → β) →
          (Fin M → Fin d → Address b N → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          ∃ r : Fin N, root r = Sum.inr 0 ∧
          ∃ cone : Fin M → Sum (Fin d → Address b N → β) (Fin 1),
            (∀ v : Fin 1, ∃ j : Fin M, cone j = Sum.inr v) ∧
            ∃ color : γ,
              ∀ σ : Fin 1 → Fin d → β,
                ∀ τ : Fin d → Fin b → β,
                  C (SpanAudit.eval root σ)
                    (coneEvaluation hb r fallback cone τ) = color := by
  obtain ⟨N, M, h⟩ :=
    HigherConeAddresses.exists_uniform_root_and_address_cones b β γ d
  refine ⟨N, M, ?_⟩
  intro C
  obtain ⟨root, hroot, cone, hcone, color, hmono⟩ := h C
  obtain ⟨r, hr⟩ := hroot 0
  refine ⟨root, r, hr, cone, hcone, color, ?_⟩
  intro σ τ
  exact hmono σ (fun _ : Fin 1 => freezeAssignment hb r fallback τ)

end DualTree.HigherConeRectangular
