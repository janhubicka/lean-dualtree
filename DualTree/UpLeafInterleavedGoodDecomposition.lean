import DualTree.UpLeafInterleavedGoodCriterion

/-!
# A three-obligation interface for actual height-one mixed c-Goodness

On the full parameter image of the genuine D₀/D₁/D₂ mixed word,
Definition-11 Good is exactly the conjunction of:

* D₀-flat substitution invariance (already supplied by parameter HJ
  on suitable chosen words);
* D₁ ambient-leaf direction invariance;
* D₁ support-letter invariance at fixed D₂ observations.

The last two conditions are the genuine remaining tree Ramsey input.
They are NOT derived from Lemma-14 UpCanonical: the adversarial
up-leaf colouring in UpLeafInterleavedGoodCriterion prevents that.

These three conditions are equivalent to Good on the *actual* source
mixed span; this is not a positive Good existence theorem.
-/

namespace DualTree.UpLeafInterleavedGoodDecomposition

open DualTree.MixedProduct
open DualTree.UpLeafInterleavedParameters
open DualTree.UpLeafInterleavedGoodCriterion
open DualTree.InterleavedFlatHalesJewett
open DualTree.ShiftedRaySlots

/-- The independently observed D₂ root letters agree. -/
def SameBulletLetters
    {d : Nat} {β : Type*}
    (kind : Fin d → CoordKind)
    (a a' : NonplainIndex kind → β) : Prop :=
  ∀ i : BulletIndex kind,
    a (bulletAsNonplain kind i) = a' (bulletAsNonplain kind i)

/-- The actual colour, evaluated on fully independent mixed parameters
after selecting the synchronized flat Hales--Jewett word. -/
noncomputable def parameterColor
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (color : Element b (ambient d N) d β kind → γ)
    (σ : PlainIndex kind → Fin 1 → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b) : γ :=
  color (parameterElement hb kind fallback
    (fun i => SpanAudit.eval (project w i) (σ i)) a directions)

/-- Erase the entire independent D₀ substitution tuple, while fixing
D₁/D₂ letters and D₁ leaf directions. -/
def PlainInvariant
    {b d : Nat} {β γ : Type*}
    (kind : Fin d → CoordKind)
    (C : (PlainIndex kind → Fin 1 → β) →
      (NonplainIndex kind → β) →
      (UpIndex kind → Fin b) → γ) : Prop :=
  ∀ σ τ a directions, C σ a directions = C τ a directions

/-- Erase the chosen D₁ leaf direction tuple, keeping all letters and
D₀ substitutions fixed. -/
def UpDirectionInvariant
    {b d : Nat} {β γ : Type*}
    (kind : Fin d → CoordKind)
    (C : (PlainIndex kind → Fin 1 → β) →
      (NonplainIndex kind → β) →
      (UpIndex kind → Fin b) → γ) : Prop :=
  ∀ σ a directions directions',
    C σ a directions = C σ a directions'

/-- Erase all nonbullet D₁ root letters, while retaining the actual
D₂ marker letters and fixed D₀ substitutions/D₁ leaf directions. -/
def UpLetterInvariant
    {b d : Nat} {β γ : Type*}
    (kind : Fin d → CoordKind)
    (C : (PlainIndex kind → Fin 1 → β) →
      (NonplainIndex kind → β) →
      (UpIndex kind → Fin b) → γ) : Prop :=
  ∀ σ a a' directions,
    SameBulletLetters kind a a' →
      C σ a directions = C σ a' directions

/-- EXACT decomposition of Definition-11 Good on the actual source
height-one interleaved mixed span into three independent obligations.
In particular, finite Hales--Jewett discharges only the first one;
the other two are genuine D₁ Ramsey tasks, not formal consequences
of UpCanonical. -/
theorem good_iff_three_invariances
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    Good color
        (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
          r hroot hfirst) ↔
      PlainInvariant kind (parameterColor hb kind w fallback color) ∧
      UpDirectionInvariant kind (parameterColor hb kind w fallback color) ∧
      UpLetterInvariant kind (parameterColor hb kind w fallback color) := by
  rw [good_iff_parameter_bullet_constancy hb kind w fallback
    r hroot hfirst color]
  constructor
  · intro hgood
    refine ⟨?_, ?_, ?_⟩
    · intro σ τ a directions
      exact hgood σ τ a a directions directions (by intro i; rfl)
    · intro σ a directions directions'
      exact hgood σ σ a a directions directions' (by intro i; rfl)
    · intro σ a a' directions hbullet
      exact hgood σ σ a a' directions directions (by
        exact hbullet)
  · rintro ⟨hplain, hdirection, hletter⟩ σ τ a a' directions directions' hbullet
    calc
      parameterColor hb kind w fallback color σ a directions =
        parameterColor hb kind w fallback color τ a directions :=
          hplain σ τ a directions
      _ = parameterColor hb kind w fallback color τ a directions' :=
        hdirection τ a directions directions'
      _ = parameterColor hb kind w fallback color τ a' directions' :=
        hletter τ a a' directions' hbullet

end DualTree.UpLeafInterleavedGoodDecomposition
