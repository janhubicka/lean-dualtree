import DualTree.InterleavedRamsey

/-!
# Full exact, nonvacuous span for arbitrary interleaved D₀/D₂ kinds

The source-facing height-one mixed Ramsey existence theorem already
uses the forward representation of every genuine mixed-span element.
Here we prove the essential adversarial CONVERSE: every independently
chosen ordinary-coordinate Hales–Jewett substitution and every tuple
of marked D₂ observations is genuinely attained by an element of
that ACTUAL mixed span.

Consequently the span equals precisely the complete parameter image,
including empty D₀ or D₂ subtypes, and is explicitly nonempty when the
original alphabet has a chosen fallback letter. No independence
between variable words in different vector coordinates is assumed;
it follows from the actual componentwise span definition.
-/

namespace DualTree.InterleavedExactSpan

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.InterleavedSpan
open DualTree.ShiftedRaySlots

/-- Every independent ordinary substitution and every genuine D₂ marker
tuple is realized in the ACTUAL interleaved mixed-product span. -/
theorem parameterElement_mem_span
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : PlainIndex kind → Fin 1 → β)
    (a : BulletIndex kind → β) :
    parameterElement hb kind hnoUp fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a ∈
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst).span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : kind i = CoordKind.plain
    · let j : PlainIndex kind := ⟨i, hi⟩
      have hσ : (fun _ : Fin 1 => σ j 0) = σ j := by
        funext v
        exact (congrArg (σ j) (Fin.eq_zero v)).symm
      have hmem :
          ShiftedRayWord.embed hb i fallback
              (SpanAudit.eval (project w j) (σ j)) ∈
            (ShiftedRayWord.kWord hb i (project w j) fallback r
              (project_root w r hroot j)
              (fun t v hv => project_after_root w r hfirst j t v hv)).span := by
        rw [ShiftedRayWord.kWord_span_eq_flat_range
          hb i (project w j) fallback r
          (project_root w r hroot j)
          (fun t v hv => project_after_root w r hfirst j t v hv)]
        refine ⟨σ j 0, ?_⟩
        rw [hσ]
      simpa [InterleavedMixedWord.mixedWord,
        InterleavedMixedWord.vectorWord,
        InterleavedMixedWord.component,
        InterleavedMixedWord.plainComponent,
        parameterElement, hi, j] using hmem
    · let j : BulletIndex kind :=
        ⟨i, bullet_of_not_plain kind hnoUp i hi⟩
      have hmem :
          FixedRootMarkerWord.valueWord
              (markerPos (N := N) hb i) fallback (a j) ∈
            (FixedRootMarkerWord.kWord
              (markerPos (N := N) hb i) fallback).span :=
        FixedRootMarkerWord.valueWord_mem_span
          (markerPos (N := N) hb i) fallback (a j)
      simpa [InterleavedMixedWord.mixedWord,
        InterleavedMixedWord.vectorWord,
        InterleavedMixedWord.component,
        parameterElement, hi, j] using hmem
  · intro i
    exact False.elim (hnoUp i.1 i.2)
  · intro i
    have hi : kind i.1 ≠ CoordKind.plain := by
      intro hp
      have hbulle : kind i.1 = CoordKind.bullet := i.2
      rw [hp] at hbulle
      cases hbulle
    have hmem :
        markerPos (N := N) hb i.1 ∈
          (FixedRootMarkerWord.kWord
            (markerPos (N := N) hb i.1) fallback).support := by
      change markerPos (N := N) hb i.1 ∈
        [markerPos (N := N) hb i.1]
      simp
    simpa [InterleavedMixedWord.mixedWord,
      InterleavedMixedWord.vectorWord,
      InterleavedMixedWord.component, parameterElement, hi] using hmem

/-- The actual mixed span is exactly the FULL image of all independent
ordinary and marked parameter assignments, not a strict or empty subset. -/
theorem mixedWord_span_eq_parameter_range
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (InterleavedMixedWord.mixedWord hb kind hnoUp
      w fallback r hroot hfirst).span =
      Set.range (fun z :
          (PlainIndex kind → Fin 1 → β) × (BulletIndex kind → β) =>
        parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (z.1 i)) z.2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, a, hrepr⟩ :=
      span_element_eq_parameterElement hb kind hnoUp
        w fallback r hroot hfirst x hx
    exact ⟨⟨σ, a⟩, hrepr.symm⟩
  · rintro ⟨⟨σ, a⟩, rfl⟩
    exact parameterElement_mem_span hb kind hnoUp
      w fallback r hroot hfirst σ a

/-- A genuine mixed-span point exists for every no-D₁ coordinate pattern,
even when one (or both) index subtypes are empty. -/
theorem mixedWord_span_nonempty
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    ((InterleavedMixedWord.mixedWord hb kind hnoUp
      w fallback r hroot hfirst).span).Nonempty := by
  let σ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
  let a : BulletIndex kind → β := fun _ => fallback
  exact ⟨parameterElement hb kind hnoUp fallback
      (fun i => SpanAudit.eval (project w i) (σ i)) a,
    parameterElement_mem_span hb kind hnoUp
      w fallback r hroot hfirst σ a⟩

end DualTree.InterleavedExactSpan
