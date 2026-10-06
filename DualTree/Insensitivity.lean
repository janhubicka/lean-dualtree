import Mathlib

/-!
# A repair principle for Remark 3(ii)

The paper states that insensitivity for two alphabets `L₁` and `L₂`
implies insensitivity for their union.  This is false when the two sets are
disjoint.  The application in the proof of Theorem 8 uses consecutive pairs
`{a_j,a_{j+1}}`, which do overlap.

The following elementary lemma isolates the bridge actually needed there.
It is intentionally phrased independently of the word machinery; later files
will instantiate it for the paper's starred-insensitivity relation.
-/

namespace DualTree.Insensitivity

/-- A map is constant on a predicate. -/
def ConstantOn {α κ : Type*} (c : α → κ) (L : α → Prop) : Prop :=
  ∀ ⦃x y⦄, L x → L y → c x = c y

/--
Constancy on two overlapping pieces implies constancy on their union.
This is the abstract transitivity step missing from the unrestricted version
of Remark 3(ii).
-/
theorem constantOn_union_of_overlap {α κ : Type*}
    (c : α → κ) (L₁ L₂ : α → Prop)
    (h₁ : ConstantOn c L₁) (h₂ : ConstantOn c L₂)
    (hoverlap : ∃ z, L₁ z ∧ L₂ z) :
    ConstantOn c (fun x => L₁ x ∨ L₂ x) := by
  rcases hoverlap with ⟨z, hz₁, hz₂⟩
  intro x y hx hy
  rcases hx with hx₁ | hx₂
  · rcases hy with hy₁ | hy₂
    · exact h₁ hx₁ hy₁
    · exact (h₁ hx₁ hz₁).trans (h₂ hz₂ hy₂)
  · rcases hy with hy₁ | hy₂
    · exact (h₂ hx₂ hz₂).trans (h₁ hz₁ hy₁)
    · exact h₂ hx₂ hy₂

end DualTree.Insensitivity
