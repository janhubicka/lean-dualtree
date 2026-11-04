import DualTree.ShiftedRayWord
import DualTree.ParameterHalesJewett

/-!
# Parameter-uniform Hales–Jewett indexed by arbitrary mixed coordinates

A height-one D₀/D₂ mixed configuration may have any interleaved kind
function, not only the first-p-ordinary/last-q-marked pattern.
The finite flat Ramsey input should therefore be indexed by the
ACTUAL ordinary-coordinate subtype and parametrized by the ACTUAL
marked-coordinate subtype, not by an unjustified permutation.

This module projects a product-alphabet Hales–Jewett word onto any
ordinary coordinate, verifies that all projections have the SAME first
variable index, and proves exact independent evaluation. It then applies
the verified parameter-uniform finite Hales–Jewett theorem directly on
the finite function alphabet indexed by the genuine D₀ subtype.

Only flat word algebra is proved here; the mixed tree-word
existence theorem requires the separate shifted-ray geometry and
actual mixed-element span representation.
-/

namespace DualTree.InterleavedFlatHalesJewett

open DualTree.MixedProduct

/-- The genuine ordinary-coordinate subtype, with no reordering. -/
abbrev PlainIndex {d : Nat} (kind : Fin d → CoordKind) :=
  {i : Fin d // kind i = CoordKind.plain}

/-- Project a flat Hales–Jewett word over the ordinary-coordinate
function alphabet onto one true ordinary coordinate. -/
def project
    {N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (i : PlainIndex kind) :
    Fin N → Sum β (Fin 1) :=
  fun j =>
    match w j with
    | Sum.inl letters => Sum.inl (letters i)
    | Sum.inr v => Sum.inr v

/-- Projected flat words share the ACTUAL first variable index. -/
theorem project_root
    {N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (r : Fin N) (hroot : w r = Sum.inr 0)
    (i : PlainIndex kind) :
    project w i r = Sum.inr 0 := by
  simp [project, hroot]

/-- Every variable occurrence in a projected coordinate is later
than the same first variable of the product-alphabet word. -/
theorem project_after_root
    {N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (r : Fin N)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : PlainIndex kind)
    (j : Fin N) (v : Fin 1)
    (h : project w i j = Sum.inr v) :
    r ≤ j := by
  cases hw : w j with
  | inl letters =>
      simp [project, hw] at h
  | inr u =>
      exact hfirst j u hw

/-- Independent ordinary-coordinate substitutions coincide exactly
with evaluation of the full finite product alphabet. -/
theorem project_eval
    {N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (σ : PlainIndex kind → Fin 1 → β)
    (i : PlainIndex kind) (j : Fin N) :
    SpanAudit.eval (project w i) (σ i) j =
      (SpanAudit.eval w (fun v k => σ k v) j) i := by
  cases hw : w j with
  | inl letters =>
      simp [project, SpanAudit.eval, SpanAudit.evalSymbol, hw]
  | inr v =>
      simp [project, SpanAudit.eval, SpanAudit.evalSymbol, hw]

/-- GENUINE finite-parameter Hales–Jewett existence on the
actual interleaved ordinary and marked index subtypes.

Every ordinary coordinate receives an INDEPENDENT variable value.
Every marked coordinate supplies its INDEPENDENT retained letter.
For each fixed marked tuple, the chosen flat line is monochromatic
across ALL ordinary substitutions. Different marked tuples need NOT
have the same colour. No D₁ hypothesis is required for this
purely flat statement; no mixed tree word is yet claimed. -/
theorem exists_uniform_flat_for_kind
    {d : Nat} (kind : Fin d → CoordKind)
    (β γ : Type*) [Finite β] [Finite γ] :
    ∃ N : Nat,
      ∀ C : (PlainIndex kind → Fin N → β) →
          (BulletIndex kind → β) → γ,
        ∃ w : Fin N → Sum (PlainIndex kind → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin N, w j = Sum.inr v) ∧
          ∀ σ τ : PlainIndex kind → Fin 1 → β,
          ∀ a : BulletIndex kind → β,
            C (fun i j => SpanAudit.eval (project w i) (σ i) j) a =
            C (fun i j => SpanAudit.eval (project w i) (τ i) j) a := by
  classical
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_uniform_flat_fibre_constancy
      (PlainIndex kind → β) (BulletIndex kind → β) γ 1
  refine ⟨N, ?_⟩
  intro C
  let D : (Fin N → PlainIndex kind → β) →
      (BulletIndex kind → β) → γ :=
    fun U a => C (fun i j => U j i) a
  obtain ⟨w, hw, hconst⟩ := hN D
  refine ⟨w, hw, ?_⟩
  intro σ τ a
  have hmono :=
    hconst (fun v i => σ i v) (fun v i => τ i v) a
  change
    C (fun i j =>
      (SpanAudit.eval w (fun v k => σ k v) j) i) a =
    C (fun i j =>
      (SpanAudit.eval w (fun v k => τ k v) j) i) a at hmono
  calc
    C (fun i j => SpanAudit.eval (project w i) (σ i) j) a =
        C (fun i j =>
          (SpanAudit.eval w (fun v k => σ k v) j) i) a := by
          congr 1
          funext i j
          exact project_eval w σ i j
    _ = C (fun i j =>
          (SpanAudit.eval w (fun v k => τ k v) j) i) a := hmono
    _ = C (fun i j => SpanAudit.eval (project w i) (τ i) j) a := by
          congr 1
          funext i j
          exact (project_eval w τ i j).symm

end DualTree.InterleavedFlatHalesJewett
