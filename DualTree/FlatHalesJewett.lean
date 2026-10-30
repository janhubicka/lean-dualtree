import Mathlib.Combinatorics.HalesJewett
import DualTree.SpanAudit

/-!
# A genuine finite multidimensional Hales–Jewett input to DualTree

The corrected mixed-product Ramsey theorem has not been formalized.
However, the ordinary multidimensional Hales–Jewett theorem IS already
kernel-checked in Mathlib. Its combinatorial subspace structure has
exactly the same constant/variable word representation as
DualTree.SpanAudit: an index function into `Sum β η`.

We construct the direct bridge from Mathlib's genuine Subspace to
the actual `SpanAudit.eval` and `SpanAudit.span` notions, and
derive an honest finite monochromatic variable-word existence
theorem, for arbitrarily many independent variables `Fin k`.
Every variable must actually occur (the `proper` condition).

This is a FLAT word theorem. It DOES NOT construct k-complete skew
tree supports, vector complete skew products, D₁ leaf sets, D₂
marked points, or a smooth mixed-product c-good Ramsey witness.
It cannot silently be substituted for Theorem 13 / Corollary 22.
-/

namespace DualTree.FlatHalesJewett

/-- Mathlib's combinatorial-subspace evaluation is definitionally
the same ordinary constant/variable evaluation as SpanAudit, with
no hidden independent-variable assignment or change of alphabet. -/
theorem subspace_eval_eq
    {η β ι : Type*}
    (l : Combinatorics.Subspace η β ι)
    (σ : η → β) :
    SpanAudit.eval l.idxFun σ = (l σ : ι → β) := by
  funext i
  rw [Combinatorics.Subspace.coe_apply]
  cases h : l.idxFun i with
  | inl a =>
      simp [SpanAudit.eval, SpanAudit.evalSymbol, h]
  | inr v =>
      simp [SpanAudit.eval, SpanAudit.evalSymbol, h]

/-- The SpanAudit evaluated span of a genuine Mathlib
subspace is EXACTLY its parametrized image. This does not
assume two different alphabet letters. -/
theorem subspace_span_eq_range
    {η β ι : Type*}
    (l : Combinatorics.Subspace η β ι) :
    SpanAudit.span l.idxFun =
      Set.range (fun σ : η → β => (l σ : ι → β)) := by
  ext x
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (subspace_eval_eq l σ).symm.trans hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (subspace_eval_eq l σ).trans hσ⟩

/-- Genuine FINITE multidimensional Hales–Jewett, expressed
directly in DualTree's own constant/variable word API.

For every finite alphabet β, finite colour set γ, and desired
number k of independent variables, there is a FINITE length N
such that every γ-colouring of (Fin N → β) has a monochromatic
SpanAudit word with k *actually occurring* variables.

This is a real existence theorem, derived from Mathlib's
proved multidimensional Hales–Jewett theorem, not a
postulated uniformity hypothesis on a chosen word. -/
theorem exists_monochromatic_flat_word
    (β γ : Type*) [Finite β] [Finite γ] (k : Nat) :
    ∃ N : Nat, ∀ c : (Fin N → β) → γ,
      ∃ w : Fin N → Sum β (Fin k),
        (∀ j : Fin k, ∃ i : Fin N, w i = Sum.inr j) ∧
        ∃ col : γ, ∀ σ : Fin k → β,
          c (SpanAudit.eval w σ) = col := by
  obtain ⟨N, hN⟩ :=
    Combinatorics.Subspace.exists_mono_in_high_dimension_fin
      β γ (Fin k)
  refine ⟨N, ?_⟩
  intro c
  obtain ⟨l, hmono⟩ := hN c
  rcases hmono with ⟨col, hc⟩
  refine ⟨l.idxFun, l.proper, col, ?_⟩
  intro σ
  rw [subspace_eval_eq l σ]
  exact hc σ

/-- The same finite Ramsey existence theorem phrased as
monochromaticity on the genuine SpanAudit EVALUATED SPAN,
rather than on syntactic substitution assignments.
This is the form closest to a later mixed-product theorem. -/
theorem exists_monochromatic_flat_span
    (β γ : Type*) [Finite β] [Finite γ] (k : Nat) :
    ∃ N : Nat, ∀ c : (Fin N → β) → γ,
      ∃ w : Fin N → Sum β (Fin k),
        (∀ j : Fin k, ∃ i : Fin N, w i = Sum.inr j) ∧
        ∃ col : γ, ∀ x : Fin N → β,
          x ∈ SpanAudit.span w → c x = col := by
  obtain ⟨N, hN⟩ :=
    exists_monochromatic_flat_word β γ k
  refine ⟨N, ?_⟩
  intro c
  obtain ⟨w, hw, col, hc⟩ := hN c
  refine ⟨w, hw, col, ?_⟩
  intro x hx
  obtain ⟨σ, hσ⟩ := hx
  rw [← hσ]
  exact hc σ

end DualTree.FlatHalesJewett
