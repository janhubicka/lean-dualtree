import DualTree.InterleavedSpan

/-!
# Unconditional c-good Ramsey existence at arbitrary interleaved D₀/D₂ kinds

The source-facing mixed coordinate-kind map may alternate D₀ and D₂
coordinates in ANY order, provided it has no D₁ coordinates.
The exact forward mixed-span representation lets us apply the
previously proved finite-parameter Hales–Jewett theorem over the
function alphabet of ACTUAL ordinary coordinates, retaining the
independent tuple of ACTUAL marked-letter observations.

This constructs a genuine mixed 1-complete-skew variable word whose
span is Definition-11 c-good for EVERY finite colouring. It does
not assume a pre-existing Good word. Colours may differ between
different D₂ letter tuples; no false Γ₁ record constancy is asserted.

The converse parameter-span coverage and nonvacuity are separate
adversarial obligations. No D₁, higher intrinsic k, relative source
refinement or final dual-tree induction is asserted in this module.
-/

namespace DualTree.InterleavedRamsey

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.InterleavedSpan
open DualTree.ShiftedRaySlots

/-- Uniformity of finite flat colours for each fixed tuple of real
D₂ observations implies Definition-11 Good on the ACTUAL mixed span.
The marked-letter comparison is derived from the actual Good
hypothesis, with no identification of different retained tuples. -/
theorem mixedWord_good_of_uniform_flat
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
    (huniform :
      ∀ σ τ : PlainIndex kind → Fin 1 → β,
      ∀ a : BulletIndex kind → β,
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a) =
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (τ i)) a)) :
    Good color
      (InterleavedMixedWord.mixedWord hb kind hnoUp w fallback
        r hroot hfirst) := by
  intro x y hx hy _ hletters
  obtain ⟨σ, a, hxrepr⟩ :=
    span_element_eq_parameterElement hb kind hnoUp
      w fallback r hroot hfirst x hx
  obtain ⟨τ, a', hyrepr⟩ :=
    span_element_eq_parameterElement hb kind hnoUp
      w fallback r hroot hfirst y hy
  have haeq : a = a' := by
    funext i
    have h := hletters i
    rw [hxrepr, hyrepr] at h
    have hleft :=
      parameterElement_bullet_letter hb kind hnoUp fallback
        (fun j => SpanAudit.eval (project w j) (σ j)) a i
    have hright :=
      parameterElement_bullet_letter hb kind hnoUp fallback
        (fun j => SpanAudit.eval (project w j) (τ j)) a' i
    exact hleft.symm.trans (h.trans hright)
  calc
    color x =
        color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a) :=
      congrArg color hxrepr
    _ = color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (τ i)) a) :=
      huniform σ τ a
    _ = color (parameterElement hb kind hnoUp fallback
          (fun i => SpanAudit.eval (project w i) (τ i)) a') := by
      rw [haeq]
    _ = color y := (congrArg color hyrepr).symm

/-- POSITIVE finite-colour mixed Ramsey existence for every
arbitrary-interleaved D₀/D₂ kind with no D₁ coordinates, at intrinsic
complete-skew height ONE. The finite ambient height is chosen
BEFORE the colouring, and the true source-facing mixed word is
constructed for EVERY colouring. No Good hypothesis is supplied. -/
theorem exists_good_interleaved_height_one
    {b d : Nat} (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) :
    ∃ n : Nat,
      ∀ color : Element b n d β kind → γ,
        ∃ f : MixedProduct.VariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)) kind,
          Good color f := by
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
  refine ⟨InterleavedMixedWord.mixedWord hb kind hnoUp
    w fallback r hroot hfirst, ?_⟩
  apply mixedWord_good_of_uniform_flat
    hb kind hnoUp w fallback r hroot hfirst color
  intro σ τ a
  exact hconst σ τ a

end DualTree.InterleavedRamsey
