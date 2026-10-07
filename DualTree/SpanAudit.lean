import Mathlib

/-!
# Evaluated spans and syntactic refinement

The paper orders variable words by inclusion of their evaluated spans.  This
file isolates the algebra behind that convention, independently of the tree
geometry.

There are two qualitatively different cases.

* Over a singleton alphabet, evaluated spans forget all variable structure.
* As soon as the alphabet contains two distinct letters, span inclusion forces
  the smaller word to be obtained by uniform syntactic substitution, provided
  every variable of the larger word actually occurs.

The second statement is the implicit fact repeatedly used later in the paper.
-/

namespace DualTree.SpanAudit

/-- Interpretation of a single constant/variable symbol. -/
def evalSymbol {κ α : Type*} (σ : κ → α) : Sum α κ → α
  | Sum.inl a => a
  | Sum.inr k => σ k

/-- Evaluate a word whose entries are constants or variables. -/
def eval {ι κ α : Type*} (w : ι → Sum α κ) (σ : κ → α) : ι → α :=
  fun i => evalSymbol σ (w i)

/-- Evaluated span of a word. -/
def span {ι κ α : Type*} (w : ι → Sum α κ) : Set (ι → α) :=
  {u | ∃ σ : κ → α, eval w σ = u}

/-- Replace each source variable by either a constant or a target variable. -/
def substitute {ι κ₁ κ₂ α : Type*}
    (w : ι → Sum α κ₁) (ρ : κ₁ → Sum α κ₂) : ι → Sum α κ₂ :=
  fun i =>
    match w i with
    | Sum.inl a => Sum.inl a
    | Sum.inr k => ρ k

theorem eval_substitute {ι κ₁ κ₂ α : Type*}
    (w : ι → Sum α κ₁) (ρ : κ₁ → Sum α κ₂) (τ : κ₂ → α) :
    eval (substitute w ρ) τ =
      eval w (fun k => evalSymbol τ (ρ k)) := by
  funext i
  cases h : w i with
  | inl a =>
      simp [eval, evalSymbol, substitute, h]
  | inr k =>
      simp [eval, evalSymbol, substitute, h]

/-- Every syntactic substitution has evaluated span contained in the source span. -/
theorem span_substitute_subset {ι κ₁ κ₂ α : Type*}
    (w : ι → Sum α κ₁) (ρ : κ₁ → Sum α κ₂) :
    span (substitute w ρ) ⊆ span w := by
  intro u hu
  rcases hu with ⟨τ, hτ⟩
  refine ⟨fun k => evalSymbol τ (ρ k), ?_⟩
  exact (eval_substitute w ρ τ).symm.trans hτ

/-- The alphabet has at least two distinct letters. -/
def HasTwoLetters (α : Type*) : Prop :=
  ∃ a b : α, a ≠ b

/--
Two constant/variable symbols that have the same value under every assignment
must be identical, provided the alphabet has at least two letters.
-/
theorem symbol_eq_of_all_evals {α κ : Type*}
    (hα : HasTwoLetters α) {x y : Sum α κ}
    (h : ∀ σ : κ → α, evalSymbol σ x = evalSymbol σ y) :
    x = y := by
  classical
  rcases hα with ⟨a₀, a₁, hne⟩
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab := h (fun _ => a₀)
          simp [evalSymbol] at hab
          simpa [hab]
      | inr k =>
          by_cases ha : a = a₀
          · have hv := h (fun _ => a₁)
            simp [evalSymbol] at hv
            have : a₀ = a₁ := by simpa [ha] using hv
            exact (hne this).elim
          · have hv := h (fun _ => a₀)
            simp [evalSymbol] at hv
            exact (ha hv).elim
  | inr k =>
      cases y with
      | inl a =>
          by_cases ha : a = a₀
          · have hv := h (fun _ => a₁)
            simp [evalSymbol] at hv
            have : a₁ = a₀ := by simpa [ha] using hv
            exact (hne this.symm).elim
          · have hv := h (fun _ => a₀)
            simp [evalSymbol] at hv
            exact (ha hv.symm).elim
      | inr l =>
          by_cases hkl : k = l
          · subst l
            rfl
          · have hlk : l ≠ k := Ne.symm hkl
            let σ : κ → α := fun q => if q = k then a₀ else a₁
            have hv := h σ
            have : a₀ = a₁ := by
              simpa [evalSymbol, σ, hkl, hlk] using hv
            exact (hne this).elim

theorem constant_preserved_of_span_subset {ι κ₁ κ₂ α : Type*}
    (hα : HasTwoLetters α)
    (f : ι → Sum α κ₁) (g : ι → Sum α κ₂)
    (hspan : span g ⊆ span f) {i : ι} {a : α}
    (hfi : f i = Sum.inl a) :
    g i = Sum.inl a := by
  apply symbol_eq_of_all_evals hα
  intro τ
  have hg : eval g τ ∈ span g := ⟨τ, rfl⟩
  rcases hspan hg with ⟨σ, hσ⟩
  have hi := congrFun hσ i
  simpa [eval, evalSymbol, hfi] using hi.symm

theorem fibre_uniform_of_span_subset {ι κ₁ κ₂ α : Type*}
    (hα : HasTwoLetters α)
    (f : ι → Sum α κ₁) (g : ι → Sum α κ₂)
    (hspan : span g ⊆ span f) {i j : ι} {k : κ₁}
    (hfi : f i = Sum.inr k) (hfj : f j = Sum.inr k) :
    g i = g j := by
  apply symbol_eq_of_all_evals hα
  intro τ
  have hg : eval g τ ∈ span g := ⟨τ, rfl⟩
  rcases hspan hg with ⟨σ, hσ⟩
  have hi := congrFun hσ i
  have hj := congrFun hσ j
  calc
    evalSymbol τ (g i) = eval g τ i := rfl
    _ = eval f σ i := hi.symm
    _ = σ k := by simp [eval, evalSymbol, hfi]
    _ = eval f σ j := by simp [eval, evalSymbol, hfj]
    _ = eval g τ j := hj
    _ = evalSymbol τ (g j) := rfl

/--
For an alphabet with at least two letters, evaluated-span inclusion is exactly
syntactic substitution, as long as every source variable occurs.
-/
theorem span_subset_iff_substitution {ι κ₁ κ₂ α : Type*}
    (hα : HasTwoLetters α)
    (f : ι → Sum α κ₁) (g : ι → Sum α κ₂)
    (hfocc : ∀ k : κ₁, ∃ i : ι, f i = Sum.inr k) :
    span g ⊆ span f ↔ ∃ ρ : κ₁ → Sum α κ₂, g = substitute f ρ := by
  constructor
  · intro hspan
    classical
    let pos : κ₁ → ι := fun k => Classical.choose (hfocc k)
    have hpos : ∀ k : κ₁, f (pos k) = Sum.inr k := by
      intro k
      exact Classical.choose_spec (hfocc k)
    let ρ : κ₁ → Sum α κ₂ := fun k => g (pos k)
    refine ⟨ρ, ?_⟩
    funext i
    cases hfi : f i with
    | inl a =>
        have hg := constant_preserved_of_span_subset hα f g hspan hfi
        simpa [substitute, hfi] using hg
    | inr k =>
        have hg := fibre_uniform_of_span_subset hα f g hspan hfi (hpos k)
        simpa [substitute, hfi, ρ] using hg
  · rintro ⟨ρ, rfl⟩
    exact span_substitute_subset f ρ

/-- Over a one-letter alphabet, all evaluated spans coincide, even with
unrelated variable types. -/
theorem singleton_span_eq {ι κ₁ κ₂ : Type*}
    (w₁ : ι → Sum PUnit κ₁) (w₂ : ι → Sum PUnit κ₂) :
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
theorem singleton_span_subset {ι κ₁ κ₂ : Type*}
    (w₁ : ι → Sum PUnit κ₁) (w₂ : ι → Sum PUnit κ₂) :
    span w₁ ⊆ span w₂ := by
  rw [singleton_span_eq w₁ w₂]

end DualTree.SpanAudit
