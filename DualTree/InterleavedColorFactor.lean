import DualTree.InterleavedExactSpan

/-!
# Exact and unique colour factorization on the interleaved height-one span

For arbitrary D₀/D₂ interleavings without D₁ coordinates, the genuine
mixed span is exactly the full family of independent ordinary
Hales–Jewett assignments and independent marked letters.

Definition-11 c-goodness is therefore EQUIVALENT to constancy on
each fibre of the actual BulletIndex(kind)→β observed-letter tuple,
not merely implied by a flat parameter-uniform colouring lemma.
Every tuple occurs in the true mixed span, so the factor through
the observed tuple exists on the whole parameter space and is UNIQUE.

This is a fully source-facing height-one result. It does not assert
global monochromaticity between different D₂ records, does not
handle D₁, k>1, prescribed relative refinements or the final
dual-tree Ramsey induction.
-/

namespace DualTree.InterleavedColorFactor

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.InterleavedSpan
open DualTree.InterleavedExactSpan
open DualTree.ShiftedRaySlots

/-- Definition-11 Good on the ACTUAL interleaved mixed span is exactly
finite-parameter colour uniformity in all independently evaluated
D₀ Hales–Jewett variables for each fixed tuple of D₂ observations. -/
theorem good_iff_uniform_flat
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    Good color
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst) ↔
      ∀ σ τ : PlainIndex kind → Fin 1 → β,
      ∀ a : BulletIndex kind → β,
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a) =
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (τ i)) a) := by
  constructor
  · intro hgood σ τ a
    let uσ : PlainIndex kind → Fin N → β :=
      fun i => SpanAudit.eval (project w i) (σ i)
    let uτ : PlainIndex kind → Fin N → β :=
      fun i => SpanAudit.eval (project w i) (τ i)
    have hx :
        parameterElement hb kind hnoUp fallback uσ a ∈
          (InterleavedMixedWord.mixedWord hb kind hnoUp
            w fallback r hroot hfirst).span :=
      parameterElement_mem_span hb kind hnoUp
        w fallback r hroot hfirst σ a
    have hy :
        parameterElement hb kind hnoUp fallback uτ a ∈
          (InterleavedMixedWord.mixedWord hb kind hnoUp
            w fallback r hroot hfirst).span :=
      parameterElement_mem_span hb kind hnoUp
        w fallback r hroot hfirst τ a
    apply hgood hx hy
    · intro i
      rfl
    · intro i
      exact (parameterElement_bullet_letter
        hb kind hnoUp fallback uσ a i).trans
        (parameterElement_bullet_letter
          hb kind hnoUp fallback uτ a i).symm
  · exact InterleavedRamsey.mixedWord_good_of_uniform_flat
      hb kind hnoUp w fallback r hroot hfirst color

/-- The true observed-marker tuple is the complete residual colour
record on this height-one mixed span. The factor is a TOTAL function
on all D₂-letter tuples because every tuple is genuinely realized. -/
theorem good_iff_factors_through_markerTuple
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    Good color
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst) ↔
      ∃ F : (BulletIndex kind → β) → γ,
        ∀ x : Element b (ambient d N) d β kind,
          x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp w
            fallback r hroot hfirst).span →
            color x = F (markerTuple x) := by
  constructor
  · intro hgood
    let σ₀ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
    let F : (BulletIndex kind → β) → γ :=
      fun a =>
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ₀ i)) a)
    refine ⟨F, ?_⟩
    intro x hx
    obtain ⟨σ, a, hrepr⟩ :=
      span_element_eq_parameterElement hb kind hnoUp
        w fallback r hroot hfirst x hx
    have hconst :=
      (good_iff_uniform_flat hb kind hnoUp
        w fallback r hroot hfirst color).mp hgood σ σ₀ a
    have htuple : markerTuple x = a := by
      rw [hrepr]
      exact markerTuple_parameterElement hb kind hnoUp fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a
    calc
      color x =
          color (parameterElement hb kind hnoUp fallback
            (fun i => SpanAudit.eval (project w i) (σ i)) a) :=
        congrArg color hrepr
      _ = F a := hconst
      _ = F (markerTuple x) := by rw [htuple]
  · rintro ⟨F, hF⟩ x y hx hy _ hletters
    have htuple : markerTuple x = markerTuple y := by
      funext i
      exact hletters i
    calc
      color x = F (markerTuple x) := hF x hx
      _ = F (markerTuple y) := congrArg F htuple
      _ = color y := (hF y hy).symm

/-- Any two total factors of the same colour on the true mixed span
agree everywhere, since every independent marked-letter tuple occurs. -/
theorem markerTuple_factor_unique
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ)
    (F G : (BulletIndex kind → β) → γ)
    (hF : ∀ x, x ∈
      (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span →
      color x = F (markerTuple x))
    (hG : ∀ x, x ∈
      (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span →
      color x = G (markerTuple x)) :
    F = G := by
  funext a
  let σ₀ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
  let x : Element b (ambient d N) d β kind :=
    parameterElement hb kind hnoUp fallback
      (fun i => SpanAudit.eval (project w i) (σ₀ i)) a
  have hx :
      x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span :=
    parameterElement_mem_span hb kind hnoUp
      w fallback r hroot hfirst σ₀ a
  have htuple : markerTuple x = a :=
    markerTuple_parameterElement hb kind hnoUp fallback
      (fun i => SpanAudit.eval (project w i) (σ₀ i)) a
  calc
    F a = color x := by simpa only [htuple] using (hF x hx).symm
    _ = G a := by simpa only [htuple] using (hG x hx)

/-- A single unique total marker-record factor is equivalent to
Definition-11 c-goodness on this exact, nonvacuous mixed span. -/
theorem good_iff_unique_markerTuple_factor
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    Good color
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst) ↔
      ∃! F : (BulletIndex kind → β) → γ,
        ∀ x : Element b (ambient d N) d β kind,
          x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
            w fallback r hroot hfirst).span →
            color x = F (markerTuple x) := by
  constructor
  · intro hgood
    obtain ⟨F, hF⟩ :=
      (good_iff_factors_through_markerTuple hb kind hnoUp
        w fallback r hroot hfirst color).mp hgood
    refine ⟨F, hF, ?_⟩
    intro G hG
    exact markerTuple_factor_unique hb kind hnoUp
      w fallback r hroot hfirst color G F hG hF
  · rintro ⟨F, hF, _⟩
    exact (good_iff_factors_through_markerTuple hb kind hnoUp
      w fallback r hroot hfirst color).mpr ⟨F, hF⟩

end DualTree.InterleavedColorFactor
