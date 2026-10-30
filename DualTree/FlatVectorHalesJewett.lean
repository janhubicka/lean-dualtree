import DualTree.FlatHalesJewett

/-!
# A finite synchronized flat VECTOR Hales–Jewett theorem

Theorem 13 needs tree-indexed mixed-product Ramsey spaces, including
complete-skew supports and marked D₂ points. The required full mixed
Ramsey theorem is still OPEN. However, ordinary multidimensional
Hales–Jewett extends to any finite product alphabet, giving a genuine
positive Ramsey theorem for vector words.

Apply the verified flat Hales–Jewett theorem over the PRODUCT alphabet
`Fin d → β`. Each coordinate of that alphabet becomes an ordinary
β-valued word. Variable positions are shared by ALL d components,
while different components may assign their variables completely
independently. In particular the resulting monochromatic subspace
is a genuine rectangular vector product, not just a diagonal
one-parameter subspace.

We prove exact coordinate evaluation, synchronized occurrence of
EVERY requested variable and existence of a monochromatic vector
word for every finite colouring.

This is not yet a vector k-complete SKEW tree support, nor does it
handle D₁ leaf sets, D₂ marked roots, Definition-21 smoothness or
the quantitative mixed Ramsey theorem.
-/

namespace DualTree.FlatVectorHalesJewett

/-- Project a joint finite-alphabet vector word to one ordinary
coordinate word. Constants are projected coordinatewise, and
a variable index is propagated unchanged to EVERY coordinate. -/
def coordinateWord
    {d N k : Nat} {β : Type*}
    (w : Fin N → Sum (Fin d → β) (Fin k))
    (i : Fin d) (j : Fin N) : Sum β (Fin k) :=
  match w j with
  | Sum.inl letter => Sum.inl (letter i)
  | Sum.inr v => Sum.inr v

/-- Coordinatewise independent evaluations of a common joint
word agree with its evaluation over the full vector alphabet.
Thus there is no hidden diagonal restriction of variable
assignments. -/
theorem coordinate_eval
    {d N k : Nat} {β : Type*}
    (w : Fin N → Sum (Fin d → β) (Fin k))
    (σ : Fin d → Fin k → β)
    (i : Fin d) (j : Fin N) :
    SpanAudit.eval (coordinateWord w i) (σ i) j =
      (SpanAudit.eval w (fun v i => σ i v) j) i := by
  cases h : w j with
  | inl a =>
      simp [coordinateWord, SpanAudit.eval, SpanAudit.evalSymbol, h]
  | inr v =>
      simp [coordinateWord, SpanAudit.eval, SpanAudit.evalSymbol, h]

/-- Properness of the joint Hales–Jewett word implies that
every variable is present at the SAME position in all vector
components. This is stronger than separate properness of
each coordinate word. -/
theorem coordinate_occurs_of_proper
    {d N k : Nat} {β : Type*}
    (w : Fin N → Sum (Fin d → β) (Fin k))
    (hproper : ∀ v : Fin k, ∃ j : Fin N, w j = Sum.inr v)
    (v : Fin k) :
    ∃ j : Fin N, ∀ i : Fin d,
      coordinateWord w i j = Sum.inr v := by
  obtain ⟨j, hj⟩ := hproper v
  refine ⟨j, ?_⟩
  intro i
  simp [coordinateWord, hj]

/-- Genuine finite *vector* multidimensional Hales–Jewett in
the DualTree SpanAudit API. A single joint word supplies
synchronized variable positions; all d components then
evaluate those variables independently.

For any finite β, γ and desired vector size d and local
variable number k, a finite N works for EVERY γ-colouring
of the entire vector word hypercube. This is an ACTUAL
existence theorem using Mathlib's Hales–Jewett, but it
does not impose the extra complete-skew tree geometry. -/
theorem exists_monochromatic_flat_vector
    (β γ : Type*) [Finite β] [Finite γ]
    (d k : Nat) :
    ∃ N : Nat, ∀ C : (Fin d → Fin N → β) → γ,
      ∃ w : Fin N → Sum (Fin d → β) (Fin k),
        (∀ v : Fin k, ∃ j : Fin N, ∀ i : Fin d,
          coordinateWord w i j = Sum.inr v) ∧
        ∃ col : γ, ∀ σ : Fin d → Fin k → β,
          C (fun i j =>
            SpanAudit.eval (coordinateWord w i) (σ i) j) = col := by
  obtain ⟨N, hN⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word
      (Fin d → β) γ k
  refine ⟨N, ?_⟩
  intro C
  let D : (Fin N → (Fin d → β)) → γ :=
    fun U => C (fun i j => U j i)
  obtain ⟨w, hw, col, hmono⟩ := hN D
  refine ⟨w, (fun v => coordinate_occurs_of_proper w hw v), col, ?_⟩
  intro σ
  have hC := hmono (fun v i => σ i v)
  change C (fun i j =>
    (SpanAudit.eval w (fun v i => σ i v) j) i) = col at hC
  calc
    C (fun i j => SpanAudit.eval (coordinateWord w i) (σ i) j) =
        C (fun i j => (SpanAudit.eval w (fun v i => σ i v) j) i) := by
      congr 1
      funext i j
      exact coordinate_eval w σ i j
    _ = col := hC

end DualTree.FlatVectorHalesJewett
