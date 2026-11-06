import DualTree.ParameterHalesJewett

/-!
# Track C: two-stage finite Ramsey selection for genuine height-two cone data

The root Hales--Jewett line must be chosen *after* a cone line has been made
uniform over every possible root-band word. The number of cone addresses is
b ^ N, where N is the root-band length, so the bounds have to be chosen
in this order: first N, then M, then the colouring.

This theorem is an unconditional, fully rectangular finite-colouring input
for the height-two tree construction. Every root-coordinate letter and every
cone-coordinate letter is independently variable. It does *not*, on its own,
assert that these flat words can be embedded with a 2-complete skew support;
that geometric bridge is a separate Track C obligation.
-/

namespace DualTree.HigherRamseyFlat

/-- Choose a root Hales--Jewett word and, uniformly over every possible root
band, an independent cone Hales--Jewett word. The cone alphabet contains
*all* depth-N addresses and all vector coordinates. There is no hidden
assumption of a preselected root or a preselected cone line. -/
theorem exists_uniform_root_and_cones
    (b : Nat) (β γ : Type*) [Finite β] [Finite γ] (d : Nat) :
    ∃ N M : Nat,
      ∀ C : (Fin N → Fin d → β) →
          (Fin M → Fin d → Fin (b ^ N) → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin N, root j = Sum.inr v) ∧
        ∃ cone : Fin M → Sum (Fin d → Fin (b ^ N) → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin M, cone j = Sum.inr v) ∧
        ∃ col : γ,
          ∀ σ : Fin 1 → Fin d → β,
            ∀ τ : Fin 1 → Fin d → Fin (b ^ N) → β,
              C (SpanAudit.eval root σ) (SpanAudit.eval cone τ) = col := by
  obtain ⟨N, hRoot⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word (Fin d → β) γ 1
  obtain ⟨M, hCone⟩ :=
    ParameterHalesJewett.exists_uniform_flat_word
      (Fin d → Fin (b ^ N) → β) (Fin N → Fin d → β) γ 1
  refine ⟨N, M, ?_⟩
  intro C
  let coneColor :
      (Fin M → Fin d → Fin (b ^ N) → β) →
        (Fin N → Fin d → β) → γ :=
    fun y x => C x y
  obtain ⟨cone, hConeProper, F, hUniform⟩ := hCone coneColor
  obtain ⟨root, hRootProper, col, hMono⟩ := hRoot F
  refine ⟨root, hRootProper, cone, hConeProper, col, ?_⟩
  intro σ τ
  exact (hUniform τ (SpanAudit.eval root σ)).trans (hMono σ)

/-- The same positive conclusion phrased using both *evaluated spans*.
The two independent variable groups do not collapse to a diagonal line. -/
theorem exists_monochromatic_root_and_cone_spans
    (b : Nat) (β γ : Type*) [Finite β] [Finite γ] (d : Nat) :
    ∃ N M : Nat,
      ∀ C : (Fin N → Fin d → β) →
          (Fin M → Fin d → Fin (b ^ N) → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          ∃ cone : Fin M → Sum (Fin d → Fin (b ^ N) → β) (Fin 1),
            (∀ v : Fin 1, ∃ j : Fin N, root j = Sum.inr v) ∧
            (∀ v : Fin 1, ∃ j : Fin M, cone j = Sum.inr v) ∧
            ∃ col : γ,
              ∀ x : Fin N → Fin d → β,
                ∀ y : Fin M → Fin d → Fin (b ^ N) → β,
                  x ∈ SpanAudit.span root →
                  y ∈ SpanAudit.span cone →
                  C x y = col := by
  obtain ⟨N, M, h⟩ := exists_uniform_root_and_cones b β γ d
  refine ⟨N, M, ?_⟩
  intro C
  obtain ⟨root, hroot, cone, hcone, col, hcol⟩ := h C
  refine ⟨root, cone, hroot, hcone, col, ?_⟩
  intro x y hx hy
  obtain ⟨σ, hσ⟩ := hx
  obtain ⟨τ, hτ⟩ := hy
  rw [← hσ, ← hτ]
  exact hcol σ τ

end DualTree.HigherRamseyFlat
