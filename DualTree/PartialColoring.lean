import Mathlib

/-!
# Classwise extension of partial colorings

In the proof of Lemma 27, the induced coloring is first given only on the
starred subspace, but Corollary 22 asks for a smooth coloring of the entire
mixed-product space. A smoothness relation with fixed coordinate groups is
an equivalence relation. To extend a partial coloring classwise one must
show that it is constant on every equivalence class it meets.

The theorem below supplies the extension once this compatibility is proved.
It does not claim that the induced coloring of Lemma 27 satisfies that
compatibility; checking this is a separate source-facing proof obligation.
-/

namespace DualTree.PartialColoring

/-- Extend a classwise-consistent partial coloring to all equivalence classes. -/
theorem exists_equivalence_respecting_extension
    {X C : Type*}
    (R : Setoid X) (D : Set X)
    (c : {x // x ∈ D} → C)
    (fallback : C)
    (hconsistent :
      ∀ (x y : X) (hx : x ∈ D) (hy : y ∈ D),
        R.r x y → c ⟨x, hx⟩ = c ⟨y, hy⟩) :
    ∃ ctotal : X → C,
      (∀ (x : X) (hx : x ∈ D), ctotal x = c ⟨x, hx⟩) ∧
      (∀ x y : X, R.r x y → ctotal x = ctotal y) := by
  classical
  let ctotal : X → C := fun x =>
    if h : ∃ z : X, z ∈ D ∧ R.r z x then
      c ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else fallback
  refine ⟨ctotal, ?_, ?_⟩
  · intro x hx
    have hw : ∃ z : X, z ∈ D ∧ R.r z x :=
      ⟨x, hx, R.iseqv.refl x⟩
    simp only [ctotal, dif_pos hw]
    exact hconsistent (Classical.choose hw) x
      (Classical.choose_spec hw).1 hx (Classical.choose_spec hw).2
  · intro x y hxy
    by_cases hx : ∃ z : X, z ∈ D ∧ R.r z x
    · have hchosenx := Classical.choose_spec hx
      have hy : ∃ z : X, z ∈ D ∧ R.r z y :=
        ⟨Classical.choose hx, hchosenx.1,
          R.iseqv.trans hchosenx.2 hxy⟩
      have hchoseny := Classical.choose_spec hy
      have hrel : R.r (Classical.choose hx) (Classical.choose hy) :=
        R.iseqv.trans hchosenx.2
          (R.iseqv.trans hxy (R.iseqv.symm hchoseny.2))
      dsimp [ctotal]
      rw [dif_pos hx, dif_pos hy]
      exact hconsistent (Classical.choose hx) (Classical.choose hy)
        hchosenx.1 hchoseny.1 hrel
    · have hy : ¬ ∃ z : X, z ∈ D ∧ R.r z y := by
        rintro ⟨z, hz, hzy⟩
        apply hx
        exact ⟨z, hz, R.iseqv.trans hzy (R.iseqv.symm hxy)⟩
      simp [ctotal, hx, hy]

/-- An extension preserving classes restricts to a classwise-consistent coloring. -/
theorem partial_coloring_compatible_of_extension
    {X C : Type*}
    (R : Setoid X) (D : Set X)
    (c : {x // x ∈ D} → C)
    (ctotal : X → C)
    (hagrees : ∀ (x : X) (hx : x ∈ D),
      ctotal x = c ⟨x, hx⟩)
    (hclass : ∀ x y : X, R.r x y → ctotal x = ctotal y) :
    ∀ (x y : X) (hx : x ∈ D) (hy : y ∈ D),
      R.r x y → c ⟨x, hx⟩ = c ⟨y, hy⟩ := by
  intro x y hx hy hxy
  calc
    c ⟨x, hx⟩ = ctotal x := (hagrees x hx).symm
    _ = ctotal y := hclass x y hxy
    _ = c ⟨y, hy⟩ := hagrees y hy

end DualTree.PartialColoring
