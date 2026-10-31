import DualTree.FlatHalesJewett

/-!
# Finite-parameter Hales–Jewett for a mixed D₀/D₂ Ramsey step

A c-good mixed-product word need not be monochromatic, since the
colour may depend on the observed D₂ letters. The appropriate finite
Hales–Jewett input is instead a word on which the colour is constant
in the D₀ variable assignments for EVERY value of a finite parameter
tuple representing the D₂ observations.

This is a genuine existence theorem. Apply the already kernel-checked
multidimensional Hales–Jewett theorem with target colours θ → γ,
where θ is the finite parameter space, and extract equality at each
parameter via function extensionality. The variable letters of the
source word remain FREE, including at the first occurrence.

The theorem does not assert equal colours for DIFFERENT parameters;
no false Γ₁ record-constancy is inferred. Its next application is a
tree-geometric block construction with D₂ marker positions fixed
outside the D₀ variable blocks.
-/

namespace DualTree.ParameterHalesJewett

/-- A finite Hales–Jewett subspace whose image colours are constant
in the variable assignment, SIMULTANEOUSLY for every parameter θ.
Different parameters may have different colours. -/
theorem exists_uniform_flat_word
    (β θ γ : Type*) [Finite β] [Finite θ] [Finite γ]
    (k : Nat) :
    ∃ N : Nat, ∀ C : (Fin N → β) → θ → γ,
      ∃ w : Fin N → Sum β (Fin k),
        (∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v) ∧
        ∃ F : θ → γ, ∀ σ : Fin k → β, ∀ t : θ,
          C (SpanAudit.eval w σ) t = F t := by
  obtain ⟨N, hN⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word
      β (θ → γ) k
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨w, hw, F, hF⟩ := hN C
  refine ⟨w, hw, F, ?_⟩
  intro σ t
  exact congrFun (hF σ) t

/-- A genuine *relative* finite Ramsey conclusion: for each fixed
parameter t, two independent evaluations of the chosen variable
word get the SAME colour. No common colour across distinct t is
asserted or needed. -/
theorem exists_uniform_flat_fibre_constancy
    (β θ γ : Type*) [Finite β] [Finite θ] [Finite γ]
    (k : Nat) :
    ∃ N : Nat, ∀ C : (Fin N → β) → θ → γ,
      ∃ w : Fin N → Sum β (Fin k),
        (∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v) ∧
        ∀ σ τ : Fin k → β, ∀ t : θ,
          C (SpanAudit.eval w σ) t =
            C (SpanAudit.eval w τ) t := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_flat_word β θ γ k
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨w, hw, F, hF⟩ := hN C
  refine ⟨w, hw, ?_⟩
  intro σ τ t
  exact (hF σ t).trans (hF τ t).symm

/-- The D₂-LETTER parameter case, with *one* independent
D₀ variable and a freely chosen D₂ letter. This is exactly
the flat colour dependence needed for the first nontrivial
two-coordinate D₀/D₂ mixed-product geometry. -/
theorem exists_one_variable_uniform_in_bullet_letter
    (β γ : Type*) [Finite β] [Finite γ] :
    ∃ N : Nat, ∀ C : (Fin N → β) → β → γ,
      ∃ w : Fin N → Sum β (Fin 1),
        (∃ j : Fin N, w j = Sum.inr 0) ∧
        ∀ σ τ : Fin 1 → β, ∀ a : β,
          C (SpanAudit.eval w σ) a =
            C (SpanAudit.eval w τ) a := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_flat_fibre_constancy β β γ 1
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨w, hw, hconst⟩ := hN C
  exact ⟨w, hw 0, hconst⟩

end DualTree.ParameterHalesJewett
