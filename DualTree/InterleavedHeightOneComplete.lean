import DualTree.InterleavedColorFactor

/-!
# Completed nonvacuous c-good height-one Ramsey theorem for D₀/D₂ interleavings

The preceding source-facing constructions jointly give a single strong
positive theorem: every finite colouring of an actual no-D₁ mixed
product admits a true vector 1-complete-skew mixed word whose
evaluated span is NONEMPTY and c-good. The colour on that span factors
uniquely through its actual marked D₂ letter record.

This theorem does not assume a homogeneous word, a Good predicate, a
nonempty span or an auxiliary parameter representation. All are
constructed from finite-parameter Hales–Jewett and verified
shifted-ray/fixed-marker component words.

Only intrinsic k=1, arbitrary D₀/D₂ interleavings and no D₁ positions
are asserted. There is no relative-source refinement, higher-k
induction, corrected Lemma-27 Q transfer or full Theorem 3 claim.
-/

namespace DualTree.InterleavedHeightOneComplete

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.ShiftedRaySlots

/-- A genuinely NONVACUOUS unconditional finite mixed Ramsey theorem at
intrinsic height one for an arbitrary fixed D₀/D₂ coordinate kind.
The selected c-good word has a real point in its span, and its colour
has a unique total factor through the true D₂ marker observations. -/
theorem exists_good_nonempty_unique_factor_height_one
    {b d : Nat} (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) :
    ∃ n : Nat,
      ∀ color : Element b n d β kind → γ,
        ∃ f : MixedProduct.VariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)) kind,
          Good color f ∧ f.span.Nonempty ∧
            ∃! F : (BulletIndex kind → β) → γ,
              ∀ x : Element b n d β kind,
                x ∈ f.span → color x = F (markerTuple x) := by
  classical
  obtain ⟨N, hN⟩ :=
    InterleavedFlatHalesJewett.exists_uniform_flat_for_kind
      kind β γ
  refine ⟨ambient d N, ?_⟩
  intro color
  let C : (PlainIndex kind → Fin N → β) →
      (BulletIndex kind → β) → γ :=
    fun u a => color (parameterElement hb kind hnoUp fallback u a)
  obtain ⟨w, hproper, hconst⟩ := hN C
  obtain ⟨r, hroot, hfirst⟩ :=
    RayHalesJewett.exists_first_variable_index w hproper
  let f := InterleavedMixedWord.mixedWord hb kind hnoUp
    w fallback r hroot hfirst
  have hgood : Good color f := by
    apply InterleavedRamsey.mixedWord_good_of_uniform_flat
      hb kind hnoUp w fallback r hroot hfirst color
    intro σ τ a
    exact hconst σ τ a
  have hnon : f.span.Nonempty :=
    InterleavedExactSpan.mixedWord_span_nonempty
      hb kind hnoUp w fallback r hroot hfirst
  have hfactor :
      ∃! F : (BulletIndex kind → β) → γ,
        ∀ x : Element b (ambient d N) d β kind,
          x ∈ f.span → color x = F (markerTuple x) :=
    (InterleavedColorFactor.good_iff_unique_markerTuple_factor
      hb kind hnoUp w fallback r hroot hfirst color).mp hgood
  exact ⟨f, hgood, hnon, hfactor⟩

end DualTree.InterleavedHeightOneComplete
