import Mathlib

/-!
# Source-facing starred insensitivity relation

Definition 30 says that two substitutions may differ at an unmarked coordinate
only when both letters lie in the chosen set `L`.  This file isolates that
relation before we add the surrounding variable-word machinery.

It also gives a kernel-checked counterexample to the unrestricted union claim
in Remark 3(ii): insensitivity for two disjoint singleton sets imposes no
change, while their union permits a genuine change.
-/

namespace DualTree.StarInsensitivity

/--
The substitution relation appearing in Definition 30, with `F` recording
the marked variable coordinates.
-/
def StarRelated {ι α : Type*}
    (L : α → Prop) (F : ι → Prop) (a b : ι → α) : Prop :=
  (∀ i, F i → a i = b i) ∧
  (∀ i, ¬ L (a i) → a i = b i) ∧
  (∀ i, ¬ L (b i) → a i = b i)

/-- A coloring is insensitive when it is constant on `StarRelated` pairs. -/
def StarInsensitive {ι α κ : Type*}
    (c : (ι → α) → κ) (L : α → Prop) (F : ι → Prop) : Prop :=
  ∀ ⦃a b⦄, StarRelated L F a b → c a = c b

/--
Equivalent pointwise form: marked coordinates agree, and every coordinate
where the substitutions differ has both letters in `L`.
-/
theorem starRelated_iff {ι α : Type*}
    {L : α → Prop} {F : ι → Prop} {a b : ι → α} :
    StarRelated L F a b ↔
      (∀ i, F i → a i = b i) ∧
      (∀ i, a i ≠ b i → L (a i) ∧ L (b i)) := by
  constructor
  · rintro ⟨hF, ha, hb⟩
    refine ⟨hF, ?_⟩
    intro i hne
    constructor
    · by_contra hnot
      exact hne (ha i hnot)
    · by_contra hnot
      exact hne (hb i hnot)
  · rintro ⟨hF, hdiff⟩
    refine ⟨hF, ?_, ?_⟩
    · intro i hnot
      by_contra hne
      exact hnot (hdiff i hne).1
    · intro i hnot
      by_contra hne
      exact hnot (hdiff i hne).2

/-- For a singleton letter set, the starred relation is equality. -/
theorem starRelated_singleton_eq {ι α : Type*}
    {z : α} {F : ι → Prop} {a b : ι → α}
    (h : StarRelated (fun x => x = z) F a b) :
    a = b := by
  funext i
  by_contra hne
  have hz := (starRelated_iff.mp h).2 i hne
  exact hne (hz.1.trans hz.2.symm)

/-- Consequently every coloring is insensitive for a singleton letter set. -/
theorem singleton_insensitive {ι α κ : Type*}
    (c : (ι → α) → κ) (z : α) (F : ι → Prop) :
    StarInsensitive c (fun x => x = z) F := by
  intro a b h
  rw [starRelated_singleton_eq h]

def noMarked (_ : Unit) : Prop := False

def boolColor (a : Unit → Bool) : Bool :=
  a ()

/--
Remark 3(ii) is false without overlap: every coloring is separately
insensitive for the singleton sets `{false}` and `{true}`, but the color
of the unique coordinate is not insensitive for their union.
-/
theorem disjoint_union_failure :
    StarInsensitive boolColor (fun x : Bool => x = false) noMarked ∧
    StarInsensitive boolColor (fun x : Bool => x = true) noMarked ∧
    ¬ StarInsensitive boolColor
        (fun x : Bool => x = false ∨ x = true) noMarked := by
  refine ⟨singleton_insensitive boolColor false noMarked,
    singleton_insensitive boolColor true noMarked, ?_⟩
  intro h
  let a : Unit → Bool := fun _ => false
  let b : Unit → Bool := fun _ => true
  have hab : StarRelated (fun x : Bool => x = false ∨ x = true)
      noMarked a b := by
    apply starRelated_iff.mpr
    constructor
    · intro i hi
      exact False.elim hi
    · intro i hne
      simp [a, b]
  have hc := h hab
  simp [boolColor, a, b] at hc

end DualTree.StarInsensitivity
