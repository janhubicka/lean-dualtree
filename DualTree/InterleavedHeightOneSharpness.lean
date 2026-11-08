import DualTree.InterleavedHeightOneComplete

/-!
# Track A adversarial sharpness of genuine interleaved height-one c-goodness

The completed NoUp height-one theorem factors colours through the *actual*
independent D₂ marker letters. It does **not** force different D₂ tuples
to have the same colour. This file records both the exact semantic
comparison with source Definition 11 and a nonvacuous, universally
parameterized counterexample to that stronger (false) conclusion.

All membership claims below concern the actual MixedProduct.VariableWord
span, not an abstract Hales--Jewett surrogate. No D₁, higher k, or
arbitrary-source relative refinement is asserted.
-/

namespace DualTree.InterleavedHeightOneSharpness

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.InterleavedParameters
open DualTree.InterleavedExactSpan
open DualTree.ShiftedRaySlots

/-- On the true interleaved height-one span, all D₂ marked *points*
are fixed. Thus source Definition-11 Good is exactly constancy on
fibres of the actual marker-letter tuple, without claiming constancy
between distinct tuples. -/
theorem good_iff_const_on_markerTuple
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
      (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst) ↔
    ∀ ⦃x y : Element b (ambient d N) d β kind⦄,
      x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span →
      y ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span →
      markerTuple x = markerTuple y →
      color x = color y := by
  constructor
  · intro hgood x y hx hy htuple
    apply hgood hx hy
    · intro i
      exact (bulletPoint_fixed_on_span
        hb kind hnoUp w fallback r hroot hfirst x hx i).trans
        (bulletPoint_fixed_on_span
          hb kind hnoUp w fallback r hroot hfirst y hy i).symm
    · intro i
      exact congrFun htuple i
  · intro hconst x y hx hy _ hletters
    apply hconst hx hy
    funext i
    exact hletters i

/-- Observing one genuine D₂ marker letter is always a c-good
colouring, including when the word has ordinary D₀ coordinates. -/
theorem observed_marker_color_good
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (i : BulletIndex kind)
    (f : MixedProduct.VariableWord b n d k β aux kind) :
    Good (fun x : Element b n d β kind => markerTuple x i) f := by
  intro x y _ _ _ hletters
  exact hletters i

/-- Whenever the alphabet has two different letters, the true mixed
span realizes both as observations at ANY selected D₂ coordinate.
This holds for arbitrary D₀/D₂ interleavings, independently of the
flat word chosen, and proves the example is not vacuous. -/
theorem two_marker_values_in_true_span
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback a₀ a₁ : β)
    (hne : a₀ ≠ a₁)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : BulletIndex kind) :
    ∃ x y : Element b (ambient d N) d β kind,
      x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span ∧
      y ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span ∧
      markerTuple x i ≠ markerTuple y i := by
  let σ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
  let u : PlainIndex kind → Fin N → β :=
    fun j => SpanAudit.eval (project w j) (σ j)
  let x : Element b (ambient d N) d β kind :=
    parameterElement hb kind hnoUp fallback u (fun _ => a₀)
  let y : Element b (ambient d N) d β kind :=
    parameterElement hb kind hnoUp fallback u (fun _ => a₁)
  have hx :
      x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span :=
    parameterElement_mem_span hb kind hnoUp
      w fallback r hroot hfirst σ (fun _ => a₀)
  have hy :
      y ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
        w fallback r hroot hfirst).span :=
    parameterElement_mem_span hb kind hnoUp
      w fallback r hroot hfirst σ (fun _ => a₁)
  have hxobs : markerTuple x i = a₀ := by
    change markerTuple
        (parameterElement hb kind hnoUp fallback u (fun _ => a₀)) i = a₀
    rw [markerTuple_parameterElement]
    rfl
  have hyobs : markerTuple y i = a₁ := by
    change markerTuple
        (parameterElement hb kind hnoUp fallback u (fun _ => a₁)) i = a₁
    rw [markerTuple_parameterElement]
    rfl
  refine ⟨x, y, hx, hy, ?_⟩
  intro heq
  exact hne (hxobs.symm.trans (heq.trans hyobs))

/-- Exact non-monochromatic sharpness: for every genuine interleaved
word with a D₂ coordinate and a two-letter alphabet, a Definition-11
c-good colouring exists whose values on its NONEMPTY true span differ.

In particular, downstream Ramsey arguments cannot replace
"factor through the retained D₂ letters" by "constant on the span". -/
theorem exists_good_but_not_monochromatic
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback a₀ a₁ : β)
    (hne : a₀ ≠ a₁)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : BulletIndex kind) :
    ∃ f : MixedProduct.VariableWord b (ambient d N) d 1 β
        (SkewTree.forwardAuxB (b := b)) kind,
      Good (fun x : Element b (ambient d N) d β kind =>
        markerTuple x i) f ∧
      ∃ x y : Element b (ambient d N) d β kind,
        x ∈ f.span ∧ y ∈ f.span ∧
        markerTuple x i ≠ markerTuple y i := by
  let f := InterleavedMixedWord.mixedWord hb kind hnoUp
    w fallback r hroot hfirst
  refine ⟨f, observed_marker_color_good i f, ?_⟩
  exact two_marker_values_in_true_span
    hb kind hnoUp w fallback a₀ a₁ hne r hroot hfirst i

/-- All total tuples of D₂ letters occur on the genuine mixed span.
This stronger, pointwise form of nonvacuity is the precise hypothesis
needed to transfer *global* monochromaticity to the residual factor. -/
theorem every_marker_tuple_realized
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
    ∀ a : BulletIndex kind → β,
      ∃ x : Element b (ambient d N) d β kind,
        x ∈ (InterleavedMixedWord.mixedWord hb kind hnoUp
          w fallback r hroot hfirst).span ∧
        markerTuple x = a := by
  intro a
  let σ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
  let u : PlainIndex kind → Fin N → β :=
    fun j => SpanAudit.eval (project w j) (σ j)
  refine ⟨parameterElement hb kind hnoUp fallback u a, ?_, ?_⟩
  · exact parameterElement_mem_span
      hb kind hnoUp w fallback r hroot hfirst σ a
  · exact markerTuple_parameterElement hb kind hnoUp fallback u a

/-- A factor through D₂ marker letters is monochromatic on the ENTIRE
span iff its total residual factor is itself constant. This equivalence
needs full realization of all marker tuples; Good alone is insufficient.
The abstract formulation is also usable in later residual-colour steps. -/
theorem monochromatic_iff_constant_total_factor
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (color : Element b n d β kind → γ)
    (F : (BulletIndex kind → β) → γ)
    (hfactor : ∀ x : Element b n d β kind,
      x ∈ f.span → color x = F (markerTuple x))
    (hfull : ∀ a : BulletIndex kind → β,
      ∃ x : Element b n d β kind,
        x ∈ f.span ∧ markerTuple x = a) :
    (∀ x y : Element b n d β kind,
      x ∈ f.span → y ∈ f.span → color x = color y) ↔
    (∀ a a' : BulletIndex kind → β, F a = F a') := by
  constructor
  · intro hmono a a'
    obtain ⟨x, hx, hxa⟩ := hfull a
    obtain ⟨y, hy, hya⟩ := hfull a'
    calc
      F a = color x := by
        simpa only [hxa] using (hfactor x hx).symm
      _ = color y := hmono x y hx hy
      _ = F a' := by
        simpa only [hya] using hfactor y hy
  · intro hconst x y hx hy
    calc
      color x = F (markerTuple x) := hfactor x hx
      _ = F (markerTuple y) := hconst _ _
      _ = color y := (hfactor y hy).symm

end DualTree.InterleavedHeightOneSharpness
