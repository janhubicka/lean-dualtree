import DualTree.HigherTreeCells

/-!
# Track C: earliest Hales--Jewett occurrences for genuine tree roots

To turn a flat root/cone word into a legal tree-variable word, an arbitrary
proper occurrence is insufficient: an earlier variable occurrence would
precede its proposed support root and violate the below-root condition.
Choose the MINIMUM variable position in each flat word before building the
root and the b selected child cones. This is a genuine finite argument,
and the two-stage Hales--Jewett color remains constant for these choices.
-/

namespace DualTree.HigherFirstVariable

open HigherConeAddresses
open HigherConeFreeze
open HigherConeRectangular

/-- A proper finite word has a least occurrence of any prescribed variable. -/
theorem exists_first_occurrence
    {N : Nat} {α κ : Type*}
    (w : Fin N → Sum α κ) (v : κ)
    (hproper : ∃ j : Fin N, w j = Sum.inr v) :
    ∃ r : Fin N,
      w r = Sum.inr v ∧
      ∀ j : Fin N, w j = Sum.inr v → r ≤ j := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter (fun j => w j = Sum.inr v)
  have hS : S.Nonempty := by
    rcases hproper with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simp [S, hj]
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hm := Finset.min'_mem S hS
    simpa [S] using hm
  · intro j hj
    exact Finset.min'_le S j (by simp [S, hj])

/-- The root position and all selected cone-root positions can be chosen
as FIRST variable occurrences simultaneously. This is exactly the shape
required for the at-root/below-root laws of the later tree encoding. -/
theorem exists_monochromatic_first_root_and_cone
    (b : Nat) (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (d : Nat) (fallback : β) :
    ∃ N M : Nat,
      ∀ C : (Fin N → Fin d → β) →
          (Fin M → Fin d → Address b N → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          ∃ r : Fin N,
            root r = Sum.inr 0 ∧
            (∀ j : Fin N, root j = Sum.inr 0 → r ≤ j) ∧
          ∃ cone : Fin M → Sum (Fin d → Address b N → β) (Fin 1),
            ∃ s : Fin M,
              cone s = Sum.inr 0 ∧
              (∀ j : Fin M, cone j = Sum.inr 0 → s ≤ j) ∧
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
  obtain ⟨r, hr, hleastRoot⟩ :=
    exists_first_occurrence root 0 (hroot 0)
  obtain ⟨s, hs, hleastCone⟩ :=
    exists_first_occurrence cone 0 (hcone 0)
  refine ⟨root, r, hr, hleastRoot, cone, s, hs, hleastCone,
    color, ?_⟩
  intro σ τ
  exact hmono σ (fun _ : Fin 1 => freezeAssignment hb r fallback τ)

end DualTree.HigherFirstVariable
