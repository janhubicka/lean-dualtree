import DualTree.ParameterHalesJewett
import DualTree.FlatVectorHalesJewett

/-!
# Uniform finite-parameter VECTOR Hales–Jewett

For several ordinary D₀ coordinates and several D₂ marker letters,
the correct finite Ramsey input must select synchronized variable
positions in ALL D₀ word coordinates, allow independent substitutions
in each coordinate, and make the colour independent of these
substitutions SIMULTANEOUSLY for every retained D₂ letter tuple.

This is a genuine finite Ramsey EXISTENCE theorem, not a
conditional statement about an already c-good mixed word.
Apply the verified parameter Hales–Jewett theorem to the
finite product alphabet (Fin d → β). The additional finite
parameter type θ can be taken to be (Fin q → β), accounting
for an arbitrary finite tuple of D₂ letters.

The result is still FLAT. The complete-skew height-one
mixed geometry must separately distinguish the ordinary
variable root from the marked D₂ variable roots.
-/

namespace DualTree.ParameterVectorHalesJewett

/-- A single synchronized proper vector word works for EVERY
finite parameter value, with all d ordinary coordinates
substituted INDEPENDENTLY. The common colour is a function
F : θ → γ, not one fixed colour across different θ. -/
theorem exists_uniform_flat_vector_word
    (β θ γ : Type*) [Finite β] [Finite θ] [Finite γ]
    (d k : Nat) :
    ∃ N : Nat, ∀ C : (Fin d → Fin N → β) → θ → γ,
      ∃ w : Fin N → Sum (Fin d → β) (Fin k),
        (∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v) ∧
        ∃ F : θ → γ, ∀ σ : Fin d → Fin k → β, ∀ t : θ,
          C (fun i j =>
            SpanAudit.eval
              (FlatVectorHalesJewett.coordinateWord w i)
              (σ i) j) t = F t := by
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_uniform_flat_word
      (Fin d → β) θ γ k
  refine ⟨N, ?_⟩
  intro C
  let D : (Fin N → Fin d → β) → θ → γ :=
    fun U t => C (fun i j => U j i) t
  obtain ⟨w, hw, F, hF⟩ := hN D
  refine ⟨w, hw, F, ?_⟩
  intro σ t
  have hmono := hF (fun v i => σ i v) t
  change C (fun i j =>
    (SpanAudit.eval w (fun v i => σ i v) j) i) t = F t at hmono
  calc
    C (fun i j =>
        SpanAudit.eval
          (FlatVectorHalesJewett.coordinateWord w i)
          (σ i) j) t =
      C (fun i j =>
        (SpanAudit.eval w (fun v i => σ i v) j) i) t := by
        congr 1
        funext i j
        exact FlatVectorHalesJewett.coordinate_eval w σ i j
    _ = F t := hmono

/-- The same genuine existence result phrased as a relative
colour-equality statement: for any FIXED finite parameter,
all independent vector substitutions get the same colour. -/
theorem exists_uniform_flat_vector_fibre_constancy
    (β θ γ : Type*) [Finite β] [Finite θ] [Finite γ]
    (d k : Nat) :
    ∃ N : Nat, ∀ C : (Fin d → Fin N → β) → θ → γ,
      ∃ w : Fin N → Sum (Fin d → β) (Fin k),
        (∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v) ∧
        ∀ σ τ : Fin d → Fin k → β, ∀ t : θ,
          C (fun i j =>
            SpanAudit.eval
              (FlatVectorHalesJewett.coordinateWord w i)
              (σ i) j) t =
          C (fun i j =>
            SpanAudit.eval
              (FlatVectorHalesJewett.coordinateWord w i)
              (τ i) j) t := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_flat_vector_word β θ γ d k
  refine ⟨N, ?_⟩
  intro C
  obtain ⟨w, hw, F, hF⟩ := hN C
  refine ⟨w, hw, ?_⟩
  intro σ τ t
  exact (hF σ t).trans (hF τ t).symm

/-- The exact parameter space for q distinct D₂ coordinates:
the tuple of their β-valued observed letters.
No equation between different D₂ tuples is asserted. -/
theorem exists_uniform_flat_vector_for_bullet_letters
    (β γ : Type*) [Finite β] [Finite γ]
    (d q k : Nat) :
    ∃ N : Nat,
      ∀ C : (Fin d → Fin N → β) → (Fin q → β) → γ,
        ∃ w : Fin N → Sum (Fin d → β) (Fin k),
          (∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v) ∧
          ∀ σ τ : Fin d → Fin k → β,
            ∀ a : Fin q → β,
              C (fun i j =>
                SpanAudit.eval
                  (FlatVectorHalesJewett.coordinateWord w i)
                  (σ i) j) a =
              C (fun i j =>
                SpanAudit.eval
                  (FlatVectorHalesJewett.coordinateWord w i)
                  (τ i) j) a := by
  exact exists_uniform_flat_vector_fibre_constancy
    β (Fin q → β) γ d k

end DualTree.ParameterVectorHalesJewett
