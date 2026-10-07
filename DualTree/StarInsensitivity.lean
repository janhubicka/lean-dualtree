import DualTree.Insensitivity

/-!
# Exact overlap repair for Appendix Remark 3(ii)

Definition 30 says that two assignments may differ, away from the marked
coordinates, only when both values lie in the chosen set L.  The paper claims
that L1-star and L2-star insensitivity imply (L1 union L2)-star insensitivity.
This is false for disjoint sets.

The actual application uses consecutive two-letter sets, hence nonempty
overlap.  This file proves the correct overlap version at the assignment
relation level.  The statement is independent of the Hales--Jewett word that
generated the subspace, so it can later be instantiated directly inside the
paper's Definition 30.
-/

namespace DualTree.StarInsensitivity

open Set

/--
Assignment relation underlying Definition 30:
marked coordinates are fixed, and every changed unmarked coordinate has both
its old and new values in L.
-/
def Related {ι α : Type*}
    (L : Set α) (F : Set ι) (a b : ι → α) : Prop :=
  (∀ i, i ∈ F → a i = b i) ∧
    ∀ i, a i ≠ b i → a i ∈ L ∧ b i ∈ L

/-- The compact relation above is equivalent to the three printed clauses. -/
theorem related_iff_printed {ι α : Type*}
    (L : Set α) (F : Set ι) (a b : ι → α) :
    Related L F a b ↔
      (∀ i, i ∈ F → a i = b i) ∧
      (∀ i, a i ∉ L → a i = b i) ∧
      (∀ i, b i ∉ L → a i = b i) := by
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro i hai
      by_contra hne
      exact hai (h.2 i hne).1
    · intro i hbi
      by_contra hne
      exact hbi (h.2 i hne).2
  · rintro ⟨hF, ha, hb⟩
    refine ⟨hF, ?_⟩
    intro i hne
    constructor
    · by_contra hnot
      exact hne (ha i hnot)
    · by_contra hnot
      exact hne (hb i hnot)

theorem related_refl {ι α : Type*}
    (L : Set α) (F : Set ι) (a : ι → α) :
    Related L F a a := by
  constructor
  · intro i hi
    rfl
  · intro i hne
    exact (hne rfl).elim

theorem related_symm {ι α : Type*}
    {L : Set α} {F : Set ι} {a b : ι → α}
    (h : Related L F a b) :
    Related L F b a := by
  constructor
  · intro i hi
    exact (h.1 i hi).symm
  · intro i hne
    have hab : a i ≠ b i := by
      intro heq
      exact hne heq.symm
    exact ⟨(h.2 i hab).2, (h.2 i hab).1⟩

/-- A coloring is L-star insensitive at the fixed marked set F. -/
def Insensitive {ι α γ : Type*}
    (c : (ι → α) → γ) (L : Set α) (F : Set ι) : Prop :=
  ∀ ⦃a b⦄, Related L F a b → c a = c b

/--
Normalize all unmarked coordinates whose values lie in L to a chosen bridge
letter z.
-/
noncomputable def normalize {ι α : Type*}
    (z : α) (L : Set α) (F : Set ι) (a : ι → α) : ι → α :=
  fun i =>
    letI : Decidable (i ∈ F) := Classical.propComplete _
    letI : Decidable (a i ∈ L) := Classical.propComplete _
    if i ∈ F then a i
    else if a i ∈ L then z
    else a i

theorem normalize_of_marked {ι α : Type*}
    {z : α} {L : Set α} {F : Set ι} {a : ι → α} {i : ι}
    (hi : i ∈ F) :
    normalize z L F a i = a i := by
  classical
  simp [normalize, hi]

theorem normalize_of_unmarked_mem {ι α : Type*}
    {z : α} {L : Set α} {F : Set ι} {a : ι → α} {i : ι}
    (hi : i ∉ F) (ha : a i ∈ L) :
    normalize z L F a i = z := by
  classical
  simp [normalize, hi, ha]

theorem normalize_of_unmarked_not_mem {ι α : Type*}
    {z : α} {L : Set α} {F : Set ι} {a : ι → α} {i : ι}
    (hi : i ∉ F) (ha : a i ∉ L) :
    normalize z L F a i = a i := by
  classical
  simp [normalize, hi, ha]

theorem related_normalize {ι α : Type*}
    {z : α} {L : Set α} {F : Set ι} {a : ι → α}
    (hz : z ∈ L) :
    Related L F a (normalize z L F a) := by
  classical
  constructor
  · intro i hi
    exact normalize_of_marked hi |>.symm
  · intro i hne
    by_cases hi : i ∈ F
    · exact (hne (normalize_of_marked hi).symm).elim
    · by_cases ha : a i ∈ L
      · refine ⟨ha, ?_⟩
        rw [normalize_of_unmarked_mem hi ha]
        exact hz
      · exact (hne (normalize_of_unmarked_not_mem hi ha).symm).elim

theorem normalize_two_of_mem_union {ι α : Type*}
    {z : α} {L₁ L₂ : Set α} {F : Set ι} {a : ι → α} {i : ι}
    (hz₂ : z ∈ L₂) (hi : i ∉ F)
    (ha : a i ∈ L₁ ∪ L₂) :
    normalize z L₂ F (normalize z L₁ F a) i = z := by
  classical
  rcases ha with ha₁ | ha₂
  · have hfirst : normalize z L₁ F a i = z :=
      normalize_of_unmarked_mem hi ha₁
    have hmem : normalize z L₁ F a i ∈ L₂ := by
      rw [hfirst]
      exact hz₂
    exact normalize_of_unmarked_mem hi hmem
  · by_cases ha₁ : a i ∈ L₁
    · have hfirst : normalize z L₁ F a i = z :=
        normalize_of_unmarked_mem hi ha₁
      have hmem : normalize z L₁ F a i ∈ L₂ := by
        rw [hfirst]
        exact hz₂
      exact normalize_of_unmarked_mem hi hmem
    · have hfirst : normalize z L₁ F a i = a i :=
        normalize_of_unmarked_not_mem hi ha₁
      have hmem : normalize z L₁ F a i ∈ L₂ := by
        rw [hfirst]
        exact ha₂
      exact normalize_of_unmarked_mem hi hmem

theorem normalize_two_of_not_mem_union {ι α : Type*}
    {z : α} {L₁ L₂ : Set α} {F : Set ι} {a : ι → α} {i : ι}
    (hi : i ∉ F) (ha : a i ∉ L₁ ∪ L₂) :
    normalize z L₂ F (normalize z L₁ F a) i = a i := by
  classical
  have ha₁ : a i ∉ L₁ := by
    intro h
    exact ha (Or.inl h)
  have ha₂ : a i ∉ L₂ := by
    intro h
    exact ha (Or.inr h)
  have hfirst : normalize z L₁ F a i = a i :=
    normalize_of_unmarked_not_mem hi ha₁
  have hnot : normalize z L₁ F a i ∉ L₂ := by
    rw [hfirst]
    exact ha₂
  calc
    normalize z L₂ F (normalize z L₁ F a) i =
        normalize z L₁ F a i := normalize_of_unmarked_not_mem hi hnot
    _ = a i := hfirst

/--
Two successive normalizations, first through L1 and then through L2, depend
only on the (L1 union L2)-star equivalence class when the chosen bridge letter
lies in both sets.
-/
theorem normalize_two_eq_of_related_union {ι α : Type*}
    {z : α} {L₁ L₂ : Set α} {F : Set ι} {a b : ι → α}
    (hz₁ : z ∈ L₁) (hz₂ : z ∈ L₂)
    (hab : Related (L₁ ∪ L₂) F a b) :
    normalize z L₂ F (normalize z L₁ F a) =
      normalize z L₂ F (normalize z L₁ F b) := by
  classical
  funext i
  by_cases hi : i ∈ F
  · calc
      normalize z L₂ F (normalize z L₁ F a) i =
          normalize z L₁ F a i := normalize_of_marked hi
      _ = a i := normalize_of_marked hi
      _ = b i := hab.1 i hi
      _ = normalize z L₁ F b i := (normalize_of_marked hi).symm
      _ = normalize z L₂ F (normalize z L₁ F b) i :=
          (normalize_of_marked hi).symm
  · by_cases ha : a i ∈ L₁ ∪ L₂
    · have hb : b i ∈ L₁ ∪ L₂ := by
        by_contra hnb
        have hne : a i ≠ b i := by
          intro heq
          apply hnb
          simpa [heq] using ha
        exact hnb (hab.2 i hne).2
      calc
        normalize z L₂ F (normalize z L₁ F a) i = z :=
          normalize_two_of_mem_union hz₂ hi ha
        _ = normalize z L₂ F (normalize z L₁ F b) i :=
          (normalize_two_of_mem_union hz₂ hi hb).symm
    · have heq : a i = b i := by
        by_contra hne
        exact ha (hab.2 i hne).1
      have hb : b i ∉ L₁ ∪ L₂ := by
        simpa [heq] using ha
      calc
        normalize z L₂ F (normalize z L₁ F a) i = a i :=
          normalize_two_of_not_mem_union hi ha
        _ = b i := heq
        _ = normalize z L₂ F (normalize z L₁ F b) i :=
          (normalize_two_of_not_mem_union hi hb).symm

/--
Corrected Remark 3(ii): overlapping insensitive sets may be united.
-/
theorem insensitive_union_of_overlap {ι α γ : Type*}
    (c : (ι → α) → γ) (F : Set ι) (L₁ L₂ : Set α)
    (h₁ : Insensitive c L₁ F)
    (h₂ : Insensitive c L₂ F)
    (hoverlap : ∃ z, z ∈ L₁ ∧ z ∈ L₂) :
    Insensitive c (L₁ ∪ L₂) F := by
  classical
  rcases hoverlap with ⟨z, hz₁, hz₂⟩
  intro a b hab
  let a₁ := normalize z L₁ F a
  let a₂ := normalize z L₂ F a₁
  let b₁ := normalize z L₁ F b
  let b₂ := normalize z L₂ F b₁
  have ha₁ : Related L₁ F a a₁ := by
    simpa [a₁] using related_normalize (a := a) hz₁
  have ha₂ : Related L₂ F a₁ a₂ := by
    simpa [a₂] using related_normalize (a := a₁) hz₂
  have hb₁ : Related L₁ F b b₁ := by
    simpa [b₁] using related_normalize (a := b) hz₁
  have hb₂ : Related L₂ F b₁ b₂ := by
    simpa [b₂] using related_normalize (a := b₁) hz₂
  have hcanon : a₂ = b₂ := by
    simpa [a₁, a₂, b₁, b₂] using
      normalize_two_eq_of_related_union (z := z) hz₁ hz₂ hab
  calc
    c a = c a₁ := h₁ ha₁
    _ = c a₂ := h₂ ha₂
    _ = c b₂ := congrArg c hcanon
    _ = c b₁ := (h₂ hb₂).symm
    _ = c b := (h₁ hb₁).symm

end DualTree.StarInsensitivity
