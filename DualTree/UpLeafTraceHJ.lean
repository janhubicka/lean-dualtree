import DualTree.InterleavedFlatHalesJewett

/-!
# Parameter-uniform flat Hales--Jewett with genuine D₁ trace parameters

This is the finite flat Ramsey input for a future height-one mixed D₀/D₁
construction.  At a fixed singleton D₁ support, a genuine chosen leaf
and its root letter are recorded by `Fin b × β`.  By
`UpLeafCanonical.parameterElement_sameUpTrace_iff`, such pairs record the
D₁ trace exactly for the previously constructed fixed-root family.

The extra D₂ parameter is retained independently: the colour may vary with
the D₁ trace *and* the D₂ tuple.  The theorem only erases the D₀ flat
substitutions, uniformly over both parameters.

This is not a proof of Definition-11 Good: it does not erase D₁ choices.
It is also not a mixed-tree existence theorem.  The upcoming bridge must
construct the actual interleaved shifted-ray components with genuine
D₁ ambient leaves and prove full evaluated-span coverage.
-/

namespace DualTree.UpLeafTraceHJ

open DualTree.MixedProduct
open DualTree.InterleavedFlatHalesJewett

/-- A single genuine proper flat word eliminates dependence on every D₀
substitution simultaneously, for each fixed tuple of D₁ branch/root-letter
observations and D₂ root letters.  Both parameter tuples remain free. -/
theorem exists_uniform_plain_given_up_and_bullet
    {b d : Nat} (kind : Fin d → CoordKind)
    (β γ : Type*) [Finite β] [Finite γ] :
    ∃ N : Nat,
      ∀ C : (PlainIndex kind → Fin N → β) →
          (UpIndex kind → Fin b × β) →
          (BulletIndex kind → β) → γ,
        ∃ w : Fin N → Sum (PlainIndex kind → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin N, w j = Sum.inr v) ∧
          ∀ σ τ : PlainIndex kind → Fin 1 → β,
          ∀ u : UpIndex kind → Fin b × β,
          ∀ a : BulletIndex kind → β,
            C (fun i j => SpanAudit.eval (project w i) (σ i) j) u a =
            C (fun i j => SpanAudit.eval (project w i) (τ i) j) u a := by
  classical
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_uniform_flat_fibre_constancy
      (PlainIndex kind → β)
      ((UpIndex kind → Fin b × β) × (BulletIndex kind → β)) γ 1
  refine ⟨N, ?_⟩
  intro C
  let D : (Fin N → PlainIndex kind → β) →
      ((UpIndex kind → Fin b × β) × (BulletIndex kind → β)) → γ :=
    fun U t => C (fun i j => U j i) t.1 t.2
  obtain ⟨w, hw, hconst⟩ := hN D
  refine ⟨w, hw, ?_⟩
  intro σ τ u a
  have hmono :=
    hconst (fun v i => σ i v) (fun v i => τ i v) (u, a)
  change
    C (fun i j =>
      (SpanAudit.eval w (fun v k => σ k v) j) i) u a =
    C (fun i j =>
      (SpanAudit.eval w (fun v k => τ k v) j) i) u a at hmono
  calc
    C (fun i j => SpanAudit.eval (project w i) (σ i) j) u a =
        C (fun i j =>
          (SpanAudit.eval w (fun v k => σ k v) j) i) u a := by
          congr 1
          funext i j
          exact project_eval w σ i j
    _ = C (fun i j =>
          (SpanAudit.eval w (fun v k => τ k v) j) i) u a := hmono
    _ = C (fun i j => SpanAudit.eval (project w i) (τ i) j) u a := by
          congr 1
          funext i j
          exact (project_eval w τ i j).symm

end DualTree.UpLeafTraceHJ
