import DualTree.InterleavedMixedWord
import DualTree.MixedGood

/-!
# Genuine mixed-product parameters for arbitrary interleaved D₀/D₂ kinds

The already checked shifted-ray slot decoder and fixed-root marker
word let us define an ACTUAL source-facing MixedProduct.Element
before choosing any Hales–Jewett word or its first variable index.

Each plain D₀ coordinate receives an independently specified flat
word embedded in its disjoint ray slots. Each D₂ coordinate receives
a word constant away from its FIXED marked root and independently
specified there. All D₂ bullet points are these actual fixed roots;
all D₁/up subtypes are empty by the given NoUp hypothesis.

The observed D₂ letters recover exactly the original independent
parameter tuple. The same fixed marker points occur for every
element of the constructed mixed span. No colour-canonization,
converse span, or positive Ramsey existence is claimed yet.
-/

namespace DualTree.InterleavedParameters

open DualTree.MixedProduct
open DualTree.InterleavedMixedWord
open DualTree.InterleavedFlatHalesJewett
open DualTree.ShiftedRaySlots

/-- Embed independent ordinary flat words and marked D₂ letters
into the ACTUAL mixed-product element type, with actual mixed index
order and no hidden reliance on the HJ first-variable position. -/
noncomputable def parameterElement
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : BulletIndex kind → β) :
    Element b (ambient d N) d β kind where
  words := fun i =>
    if hi : kind i = CoordKind.plain then
      ShiftedRayWord.embed hb i fallback (u ⟨i, hi⟩)
    else
      FixedRootMarkerWord.valueWord (markerPos hb i) fallback
        (a ⟨i, bullet_of_not_plain kind hnoUp i hi⟩)
  upPoint := fun i => False.elim (hnoUp i.1 i.2)
  bulletPoint := fun i => markerPos hb i.1

/-- Every genuine plain coordinate embeds exactly its own
independent finite flat word. -/
theorem parameterElement_plain
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : BulletIndex kind → β)
    (i : PlainIndex kind) :
    (parameterElement hb kind hnoUp fallback u a).words i.1 =
      ShiftedRayWord.embed hb i.1 fallback (u i) := by
  have hi : kind i.1 = CoordKind.plain := i.2
  simp [parameterElement, hi]

/-- Every genuine D₂ marker lies at its predetermined bounded node. -/
theorem parameterElement_bulletPoint
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : BulletIndex kind → β)
    (i : BulletIndex kind) :
    (parameterElement hb kind hnoUp fallback u a).bulletPoint i =
      markerPos hb i.1 := rfl

/-- Each ACTUAL D₂ observation is exactly its independently
specified marked-letter parameter, not an artificial common
letter for all D₂ coordinates. -/
theorem parameterElement_bullet_letter
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : BulletIndex kind → β)
    (i : BulletIndex kind) :
    (parameterElement hb kind hnoUp fallback u a).words i.1
      ((parameterElement hb kind hnoUp fallback u a).bulletPoint i) =
        a i := by
  have hi : kind i.1 ≠ CoordKind.plain := by
    intro hplain
    have hbulle : kind i.1 = CoordKind.bullet := i.2
    rw [hplain] at hbulle
    cases hbulle
  simp [parameterElement, hi, FixedRootMarkerWord.valueWord]

/-- The source-facing tuple of actually observed D₂ letters. -/
def markerTuple
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (x : Element b n d β kind) :
    BulletIndex kind → β :=
  fun i => x.words i.1 (x.bulletPoint i)

/-- The marker observation recovers the entire input parameter tuple,
including for zero or arbitrarily many interleaved marked coordinates. -/
theorem markerTuple_parameterElement
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (fallback : β)
    (u : PlainIndex kind → Fin N → β)
    (a : BulletIndex kind → β) :
    markerTuple (parameterElement hb kind hnoUp fallback u a) = a := by
  funext i
  exact parameterElement_bullet_letter hb kind hnoUp fallback u a i

/-- For ANY element of the genuine interleaved mixed span, every
D₂ marked point is the predetermined singleton support root.
This does not require, or assert, a colour-homogeneous word. -/
theorem bulletPoint_fixed_on_span
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
        r hroot hfirst).span)
    (i : BulletIndex kind) :
    x.bulletPoint i = markerPos hb i.1 := by
  have hi : kind i.1 ≠ CoordKind.plain := by
    intro hp
    have hbul : kind i.1 = CoordKind.bullet := i.2
    rw [hp] at hbul
    cases hbul
  have hmem :
      x.bulletPoint i ∈
        (FixedRootMarkerWord.kWord (markerPos hb i.1) fallback).support := by
    have h := hx.2.2 i
    simpa [InterleavedMixedWord.mixedWord,
      InterleavedMixedWord.vectorWord,
      InterleavedMixedWord.component, hi] using h
  change x.bulletPoint i ∈ [markerPos hb i.1] at hmem
  simpa using hmem

end DualTree.InterleavedParameters
