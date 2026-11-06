import DualTree.InterleavedParameters

/-!
# Genuine forward span representation for arbitrary interleaved D₀/D₂ kinds

Let the coordinate-kind map have no D₁ positions. The verified shifted-ray
and fixed-root word constructions give an actual mixed variable word of
intrinsic height one, with independent coordinate substitutions.

Every point in its TRUE `MixedProduct.VariableWord.span` is represented
by independent Hales–Jewett substitutions in the genuine D₀ index subtype
and the letters genuinely observed at the D₂ marked roots. The proof
uses exact component evaluated-span equalities, not an assumed parameter
representation or a pre-existing `Good` witness.

This is the forward inclusion needed for finite-parameter Hales–Jewett.
The converse, nonvacuity, Ramsey existence and higher-height extensions
are separate obligations.
-/

namespace DualTree.InterleavedSpan

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.ShiftedRaySlots

/-- Extensionality for genuine source-facing mixed elements. -/
theorem element_eq_of_fields
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (x y : Element b n d β kind)
    (hw : x.words = y.words)
    (hu : x.upPoint = y.upPoint)
    (hb : x.bulletPoint = y.bulletPoint) :
    x = y := by
  cases x with
  | mk wx ux bx =>
    cases y with
    | mk wy uy byy =>
      change wx = wy at hw
      change ux = uy at hu
      change bx = byy at hb
      cases hw
      cases hu
      cases hb
      rfl

/-- Every element of the ACTUAL mixed span is a parameterElement with
independently assigned projected D₀ variables and genuine D₂ letters. -/
theorem span_element_eq_parameterElement
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
    (x : Element b (ambient d N) d β kind)
    (hx : x ∈
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst).span) :
    ∃ σ : PlainIndex kind → Fin 1 → β,
    ∃ a : BulletIndex kind → β,
      x = parameterElement hb kind hnoUp fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a := by
  classical
  have hplain (i : PlainIndex kind) :
      x.words i.1 ∈
        (plainComponent hb w fallback r hroot hfirst i).span := by
    have h := hx.1 i.1
    simpa [InterleavedMixedWord.mixedWord,
      InterleavedMixedWord.vectorWord,
      InterleavedMixedWord.component, i.2] using h
  have hplainRange (i : PlainIndex kind) :
      x.words i.1 ∈
        Set.range (fun z : β =>
          ShiftedRayWord.embed hb i.1 fallback
            (SpanAudit.eval (project w i) (fun _ => z))) := by
    rw [← ShiftedRayWord.kWord_span_eq_flat_range
      hb i.1 (project w i) fallback r
      (project_root w r hroot i)
      (fun j v hv => project_after_root w r hfirst i j v hv)]
    exact hplain i
  have hchoice (i : PlainIndex kind) :
      ∃ z : β, x.words i.1 =
        ShiftedRayWord.embed hb i.1 fallback
          (SpanAudit.eval (project w i) (fun _ => z)) := by
    obtain ⟨z, hz⟩ := hplainRange i
    exact ⟨z, hz.symm⟩
  choose z hz using hchoice
  let σ : PlainIndex kind → Fin 1 → β := fun i _ => z i
  let a : BulletIndex kind → β :=
    fun i => x.words i.1 (markerPos (N := N) hb i.1)
  have hplainWord (i : PlainIndex kind) :
      x.words i.1 =
        ShiftedRayWord.embed hb i.1 fallback
          (SpanAudit.eval (project w i) (σ i)) := by
    simpa [σ] using hz i
  have hbulletWord (i : BulletIndex kind) :
      x.words i.1 =
        FixedRootMarkerWord.valueWord
          (markerPos (N := N) hb i.1) fallback (a i) := by
    have hi : kind i.1 ≠ CoordKind.plain := by
      intro hp
      have hbulle := i.2
      rw [hp] at hbulle
      cases hbulle
    have hmem :
        x.words i.1 ∈
          (FixedRootMarkerWord.kWord
            (markerPos (N := N) hb i.1) fallback).span := by
      have h := hx.1 i.1
      simpa [InterleavedMixedWord.mixedWord,
        InterleavedMixedWord.vectorWord,
        InterleavedMixedWord.component, hi] using h
    have hrange :
        x.words i.1 ∈
          Set.range (FixedRootMarkerWord.valueWord
            (markerPos (N := N) hb i.1) fallback) := by
      rw [← FixedRootMarkerWord.span_eq_range
        (markerPos (N := N) hb i.1) fallback]
      exact hmem
    obtain ⟨z', hz'⟩ := hrange
    have ha : a i = z' := by
      have h := congrFun hz' (markerPos (N := N) hb i.1)
      simpa [a, FixedRootMarkerWord.valueWord] using h.symm
    calc
      x.words i.1 =
          FixedRootMarkerWord.valueWord
            (markerPos (N := N) hb i.1) fallback z' := hz'.symm
      _ = FixedRootMarkerWord.valueWord
            (markerPos (N := N) hb i.1) fallback (a i) := by rw [ha]
  have hwords :
      x.words =
        (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a).words := by
    funext i
    by_cases hi : kind i = CoordKind.plain
    · let j : PlainIndex kind := ⟨i, hi⟩
      have h := hplainWord j
      simpa [parameterElement, hi, j] using h
    · let j : BulletIndex kind :=
        ⟨i, bullet_of_not_plain kind hnoUp i hi⟩
      have h := hbulletWord j
      simpa [parameterElement, hi, j] using h
  have hup :
      x.upPoint =
        (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a).upPoint := by
    funext i
    exact False.elim (hnoUp i.1 i.2)
  have hbullet :
      x.bulletPoint =
        (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a).bulletPoint := by
    funext i
    exact bulletPoint_fixed_on_span hb kind hnoUp
      w fallback r hroot hfirst x hx i
  refine ⟨σ, a, ?_⟩
  exact element_eq_of_fields x
    (parameterElement hb kind hnoUp fallback
      (fun i => SpanAudit.eval (project w i) (σ i)) a)
    hwords hup hbullet

end DualTree.InterleavedSpan
