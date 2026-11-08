import DualTree.UpLeafInterleavedGeometry

/-!
# Parameter points in the genuine interleaved D₀/D₁/D₂ mixed span

The parameter element is defined BEFORE any flat Hales--Jewett word is
selected. Its data are independent full flat D₀ coordinate words,
independent letters at every non-D₀ (D₁ or D₂) singleton support,
and independent real D₁ leaf directions.

We prove that after inserting the evaluated proper flat word in each
D₀ coordinate, every parameter choice is a point of the ACTUAL span
of UpLeafInterleavedGeometry.mixedWord, including its genuine up-leaf
and bullet-point membership conditions.

This is the difficult forward/nonvacuous direction of full parameter
coverage. The CONVERSE representation of an arbitrary span element,
a full span equality and any Ramsey colour-canonicalization remain
separate obligations. No Good or UpCanonical hypothesis is used.
-/

namespace DualTree.UpLeafInterleavedParameters

open DualTree.MixedProduct
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedMixedWord
open DualTree.ShiftedRaySlots
open DualTree.UpLeafGeometry

/-- The actual nonordinary coordinate subtype, without reordering. -/
abbrev NonplainIndex {d : Nat} (kind : Fin d → CoordKind) :=
  {i : Fin d // kind i ≠ CoordKind.plain}

/-- An element of the source-facing mixed product, parametrized by full
flat D₀ coordinate words, genuine nonplain root letters and D₁ directions. -/
noncomputable def parameterElement
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b) :
    Element b (ambient d N) d β kind where
  words := fun i =>
    if hi : kind i = CoordKind.plain then
      ShiftedRayWord.embed hb i fallback (u ⟨i, hi⟩)
    else
      FixedRootMarkerWord.valueWord
        (markerPos (N := N) hb i) fallback (a ⟨i, hi⟩)
  upPoint := fun i =>
    ambientLeaf hb (markerPos (N := N) hb i.1) (directions i)
  bulletPoint := fun i => markerPos (N := N) hb i.1

/-- At a D₀ coordinate the embedded word has precisely the chosen flat data. -/
theorem parameterElement_plain
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (fallback : β) (u : PlainIndex kind → Fin N → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b)
    (i : PlainIndex kind) :
    (parameterElement hb kind fallback u a directions).words i.1 =
      ShiftedRayWord.embed hb i.1 fallback (u i) := by
  simp [parameterElement, i.2]

/-- Every actual nonplain support root observes its independently chosen letter. -/
theorem parameterElement_nonplain_root_letter
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (fallback : β) (u : PlainIndex kind → Fin N → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b)
    (i : NonplainIndex kind) :
    (parameterElement hb kind fallback u a directions).words i.1
        (markerPos (N := N) hb i.1) = a i := by
  simp [parameterElement, i.2, FixedRootMarkerWord.valueWord_at_root]

/-- An up-coordinate's scheduled vector root is precisely the fixed
marker root used by its *actual* ambient leaf. -/
theorem rootPos_eq_markerPos_of_up
    {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : UpIndex kind) :
    rootPos hb r kind i.1 = markerPos (N := N) hb i.1 := by
  apply Subtype.ext
  symm
  have hi : kind i.1 ≠ CoordKind.plain := by
    intro h
    have hu : kind i.1 = CoordKind.up := i.2
    rw [h] at hu
    cases hu
  exact UpLeafInterleavedGeometry.markerPos_eq_supportRoot_of_not_plain
    hb r kind i.1 hi

/-- Genuine forward parameter coverage, including every independently
chosen D₁ ambient direction. This is a statement about the ACTUAL source
span, not merely a formal list of substitutions. -/
theorem parameterElement_mem_span
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : PlainIndex kind → Fin 1 → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b) :
    parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a directions ∈
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
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
        change ShiftedRayWord.embed hb i fallback
            (SpanAudit.eval (project w j) (fun _ : Fin 1 => σ j 0)) =
          ShiftedRayWord.embed hb i fallback
            (SpanAudit.eval (project w j) (σ j))
        rw [hσ]
      simpa [UpLeafInterleavedGeometry.mixedWord,
        UpLeafMixedWord.attach,
        UpLeafInterleavedGeometry.vectorWord,
        InterleavedMixedWord.component,
        InterleavedMixedWord.plainComponent,
        parameterElement, hi, j] using hmem
    · let j : NonplainIndex kind := ⟨i, hi⟩
      have hmem :
          FixedRootMarkerWord.valueWord
              (markerPos (N := N) hb i) fallback (a j) ∈
            (FixedRootMarkerWord.kWord
              (markerPos (N := N) hb i) fallback).span :=
        FixedRootMarkerWord.valueWord_mem_span
          (markerPos (N := N) hb i) fallback (a j)
      simpa [UpLeafInterleavedGeometry.mixedWord,
        UpLeafMixedWord.attach,
        UpLeafInterleavedGeometry.vectorWord,
        InterleavedMixedWord.component,
        parameterElement, hi, j] using hmem
  · intro i
    have hroot' := rootPos_eq_markerPos_of_up hb r kind i
    change ambientLeaf hb (markerPos (N := N) hb i.1) (directions i) ∈
      ambientLeaves hb (rootPos hb r kind i.1)
    rw [hroot']
    exact ambientLeaf_mem hb (markerPos (N := N) hb i.1) (directions i)
  · intro i
    have hi : kind i.1 ≠ CoordKind.plain := by
      intro h
      have hbulle : kind i.1 = CoordKind.bullet := i.2
      rw [h] at hbulle
      cases hbulle
    have hmem :
        markerPos (N := N) hb i.1 ∈
          (FixedRootMarkerWord.kWord
            (markerPos (N := N) hb i.1) fallback).support := by
      change markerPos (N := N) hb i.1 ∈
        [markerPos (N := N) hb i.1]
      simp
    simpa [UpLeafInterleavedGeometry.mixedWord,
      UpLeafMixedWord.attach,
      UpLeafInterleavedGeometry.vectorWord,
      InterleavedMixedWord.component,
      parameterElement, hi] using hmem

end DualTree.UpLeafInterleavedParameters
