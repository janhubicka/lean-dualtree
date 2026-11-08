import DualTree.UpLeafInterleavedParameters
import DualTree.InterleavedSpan

/-!
# Exact span of true interleaved D₀/D₁/D₂ words

Every actual span point of the interleaved shifted-ray mixed word recovers
independent D₀ substitutions, independent nonplain D₁/D₂ root letters,
and independent actual D₁ ambient directions. Combined with the
parameter-to-span theorem of UpLeafInterleavedParameters, this gives
an equality of the FULL genuine mixed span and the parameter image.

No Good or UpCanonical hypothesis is introduced. The flat Ramsey
theorem and the separate D₁ trace comparison are not used here.
-/

namespace DualTree.UpLeafInterleavedSpan

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.UpLeafInterleavedParameters
open DualTree.ShiftedRaySlots
open DualTree.UpLeafGeometry

/-- Every point of the genuine mixed span has a complete independent
parameter representation. In particular, the D₁ leaf is never invented
after the fact: its direction is recovered from actual up-leaf membership. -/
theorem span_element_eq_parameterElement
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (ambient d N) d β kind)
    (hx : x ∈
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst).span) :
    ∃ (σ : PlainIndex kind → Fin 1 → β),
    ∃ (a : NonplainIndex kind → β),
    ∃ (directions : UpIndex kind → Fin b),
      x = parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (σ i))
        a directions := by
  classical
  have hplain (i : PlainIndex kind) :
      x.words i.1 ∈
        (plainComponent hb w fallback r hroot hfirst i).span := by
    have h := hx.1 i.1
    simpa [UpLeafInterleavedGeometry.mixedWord,
      UpLeafMixedWord.attach, UpLeafInterleavedGeometry.vectorWord,
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
  let a : NonplainIndex kind → β :=
    fun i => x.words i.1 (markerPos (N := N) hb i.1)
  have hplainWord (i : PlainIndex kind) :
      x.words i.1 =
        ShiftedRayWord.embed hb i.1 fallback
          (SpanAudit.eval (project w i) (σ i)) := by
    simpa [σ] using hz i
  have hnonplainWord (i : NonplainIndex kind) :
      x.words i.1 =
        FixedRootMarkerWord.valueWord
          (markerPos (N := N) hb i.1) fallback (a i) := by
    have hmem :
        x.words i.1 ∈
          (FixedRootMarkerWord.kWord
            (markerPos (N := N) hb i.1) fallback).span := by
      have h := hx.1 i.1
      simpa [UpLeafInterleavedGeometry.mixedWord,
        UpLeafMixedWord.attach, UpLeafInterleavedGeometry.vectorWord,
        InterleavedMixedWord.component, i.2] using h
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
  have hu : ∀ i : UpIndex kind, ∃ j : Fin b,
      ambientLeaf hb (markerPos (N := N) hb i.1) j = x.upPoint i := by
    intro i
    have hmem := hx.2.1 i
    change x.upPoint i ∈ ambientLeaves hb
      (rootPos hb r kind i.1) at hmem
    rw [rootPos_eq_markerPos_of_up hb r kind i] at hmem
    exact (mem_ambientLeaves_iff hb
      (markerPos (N := N) hb i.1) (x.upPoint i)).1 hmem
  choose directions hd using hu
  have hwords :
      x.words =
        (parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a directions).words := by
    funext i
    by_cases hi : kind i = CoordKind.plain
    · let j : PlainIndex kind := ⟨i, hi⟩
      have h := hplainWord j
      simpa [parameterElement, hi, j] using h
    · let j : NonplainIndex kind := ⟨i, hi⟩
      have h := hnonplainWord j
      simpa [parameterElement, hi, j] using h
  have hup :
      x.upPoint =
        (parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a directions).upPoint := by
    funext i
    change x.upPoint i =
      ambientLeaf hb (markerPos (N := N) hb i.1) (directions i)
    exact (hd i).symm
  have hbullet :
      x.bulletPoint =
        (parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a directions).bulletPoint := by
    funext i
    have hi : kind i.1 ≠ CoordKind.plain := by
      intro hplain
      have hkind : kind i.1 = CoordKind.bullet := i.2
      rw [hplain] at hkind
      cases hkind
    have hmem :
        x.bulletPoint i ∈
          (FixedRootMarkerWord.kWord
            (markerPos (N := N) hb i.1) fallback).support := by
      have h := hx.2.2 i
      simpa [UpLeafInterleavedGeometry.mixedWord,
        UpLeafMixedWord.attach, UpLeafInterleavedGeometry.vectorWord,
        InterleavedMixedWord.component, hi] using h
    change x.bulletPoint i ∈
      [markerPos (N := N) hb i.1] at hmem
    change x.bulletPoint i = markerPos (N := N) hb i.1
    simpa using hmem
  refine ⟨σ, a, directions, ?_⟩
  exact InterleavedSpan.element_eq_of_fields x
    (parameterElement hb kind fallback
      (fun i => SpanAudit.eval (project w i) (σ i)) a directions)
    hwords hup hbullet

/-- No independently varying up or ordinary parameter is lost:
this is full equality with the ACTUAL source mixed span. -/
theorem mixedWord_span_eq_parameter_range
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
      r hroot hfirst).span =
      Set.range (fun z :
        (PlainIndex kind → Fin 1 → β) ×
          (NonplainIndex kind → β) × (UpIndex kind → Fin b) =>
        parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (z.1 i))
          z.2.1 z.2.2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, a, directions, hrepr⟩ :=
      span_element_eq_parameterElement hb kind w fallback
        r hroot hfirst x hx
    exact ⟨⟨σ, a, directions⟩, hrepr.symm⟩
  · rintro ⟨⟨σ, a, directions⟩, rfl⟩
    exact parameterElement_mem_span hb kind w fallback
      r hroot hfirst σ a directions

end DualTree.UpLeafInterleavedSpan
