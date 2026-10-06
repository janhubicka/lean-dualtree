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


/-- Replace every unmarked letter from `L` by a fixed bridge letter. -/
noncomputable def normalize {ι α : Type*}
    (L : α → Prop) (F : ι → Prop) (z : α) (a : ι → α) : ι → α := by
  classical
  exact fun i => if F i then a i else if L (a i) then z else a i

/-- Normalization is an allowed `L`-move when the bridge letter lies in `L`. -/
theorem starRelated_normalize {ι α : Type*}
    {L : α → Prop} {F : ι → Prop} {z : α} {a : ι → α}
    (hz : L z) :
    StarRelated L F a (normalize L F z a) := by
  apply starRelated_iff.mpr
  constructor
  · intro i hi
    simp [normalize, hi]
  · intro i hne
    have hFi : ¬ F i := by
      intro hi
      apply hne
      simp [normalize, hi]
    by_cases hLi : L (a i)
    · refine ⟨hLi, ?_⟩
      simpa [normalize, hFi, hLi] using hz
    · exfalso
      apply hne
      simp [normalize, hFi, hLi]

/-- Two successive normalizations send every unmarked union-letter to the bridge. -/
theorem normalize_twice_of_mem_union {ι α : Type*}
    {L₁ L₂ : α → Prop} {F : ι → Prop} {z : α} {a : ι → α} {i : ι}
    (hz₂ : L₂ z) (hFi : ¬ F i) (hi : L₁ (a i) ∨ L₂ (a i)) :
    normalize L₂ F z (normalize L₁ F z a) i = z := by
  classical
  rcases hi with h₁ | h₂
  · simp [normalize, hFi, h₁, hz₂]
  · by_cases h₁ : L₁ (a i)
    · simp [normalize, hFi, h₁, hz₂]
    · simp [normalize, hFi, h₁, h₂]

/--
Union-related substitutions have the same two-stage normal form whenever the
second normalization uses a bridge letter in `L₂`.
-/
theorem normalize_twice_eq {ι α : Type*}
    {L₁ L₂ : α → Prop} {F : ι → Prop} {z : α} {a b : ι → α}
    (hz₂ : L₂ z)
    (hab : StarRelated (fun x => L₁ x ∨ L₂ x) F a b) :
    normalize L₂ F z (normalize L₁ F z a) =
      normalize L₂ F z (normalize L₁ F z b) := by
  funext i
  by_cases hFi : F i
  · have hi := (starRelated_iff.mp hab).1 i hFi
    simp [normalize, hFi, hi]
  · by_cases hi : a i = b i
    · simp [hi]
    · have hu := (starRelated_iff.mp hab).2 i hi
      calc
        normalize L₂ F z (normalize L₁ F z a) i = z :=
          normalize_twice_of_mem_union hz₂ hFi hu.1
        _ = normalize L₂ F z (normalize L₁ F z b) i :=
          (normalize_twice_of_mem_union hz₂ hFi hu.2).symm

/--
Corrected form of Remark 3(ii): if the two letter sets overlap, separate
starred insensitivity for them implies starred insensitivity for their union.
-/
theorem starInsensitive_union_of_overlap {ι α κ : Type*}
    {c : (ι → α) → κ} {L₁ L₂ : α → Prop} {F : ι → Prop}
    (h₁ : StarInsensitive c L₁ F)
    (h₂ : StarInsensitive c L₂ F)
    (hoverlap : ∃ z, L₁ z ∧ L₂ z) :
    StarInsensitive c (fun x => L₁ x ∨ L₂ x) F := by
  rcases hoverlap with ⟨z, hz₁, hz₂⟩
  intro a b hab
  have ha₁ : c a = c (normalize L₁ F z a) :=
    h₁ (starRelated_normalize hz₁)
  have ha₂ :
      c (normalize L₁ F z a) =
        c (normalize L₂ F z (normalize L₁ F z a)) :=
    h₂ (starRelated_normalize hz₂)
  have hb₁ : c b = c (normalize L₁ F z b) :=
    h₁ (starRelated_normalize hz₁)
  have hb₂ :
      c (normalize L₁ F z b) =
        c (normalize L₂ F z (normalize L₁ F z b)) :=
    h₂ (starRelated_normalize hz₂)
  have hnormal := normalize_twice_eq hz₂ hab
  calc
    c a = c (normalize L₂ F z (normalize L₁ F z a)) := ha₁.trans ha₂
    _ = c (normalize L₂ F z (normalize L₁ F z b)) := by rw [hnormal]
    _ = c b := (hb₁.trans hb₂).symm

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
