import Mathlib

/-!
# Singleton-alphabet span collapse

The paper orders variable words by inclusion of their evaluated spans.  Over a
singleton alphabet this forgets all variable structure: every evaluated word
is the unique constant word.  This file isolates that mechanism independently
of the tree geometry.
-/

namespace DualTree.SpanAudit

/-- Evaluate a word whose entries are constants or variables. -/
def eval {ι κ α : Type*} (w : ι → Sum α κ) (σ : κ → α) : ι → α :=
  fun i =>
    match w i with
    | Sum.inl a => a
    | Sum.inr k => σ k

/-- Evaluated span of a word. -/
def span {ι κ α : Type*} (w : ι → Sum α κ) : Set (ι → α) :=
  {u | ∃ σ : κ → α, eval w σ = u}

/-- Over the one-letter alphabet `PUnit`, all evaluated spans coincide. -/
theorem singleton_span_eq {ι κ : Type*}
    (w₁ w₂ : ι → Sum PUnit κ) :
    span w₁ = span w₂ := by
  ext u
  constructor
  · intro _
    refine ⟨fun _ => PUnit.unit, ?_⟩
    exact Subsingleton.elim _ _
  · intro _
    refine ⟨fun _ => PUnit.unit, ?_⟩
    exact Subsingleton.elim _ _

/-- Hence span inclusion is universal over a singleton alphabet. -/
theorem singleton_span_subset {ι κ : Type*}
    (w₁ w₂ : ι → Sum PUnit κ) :
    span w₁ ⊆ span w₂ := by
  rw [singleton_span_eq w₁ w₂]

end DualTree.SpanAudit
