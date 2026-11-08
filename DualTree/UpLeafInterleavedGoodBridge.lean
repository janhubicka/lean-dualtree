import DualTree.UpLeafInterleavedGoodDecomposition

/-!
# UpCanonical supplies exactly the plain-coordinate invariance

On a genuine interleaved height-one word, the Lemma-14 source trace
forgets every D₀ substitution.  Thus UpCanonical already implies the
first of the three Definition-11 Good invariances. Conditional on
UpCanonical, the remaining work consists precisely of direction
and root-letter invariance for the D₁ coordinates. The statements
apply in the presence of arbitrary D₂ coordinates; no NoBullet or
two-letter hypothesis is needed.

This is a fixed-word logical bridge, not a positive Ramsey
existence theorem for the two remaining D₁ invariances.
-/

namespace DualTree.UpLeafInterleavedGoodBridge

open DualTree.MixedProduct
open DualTree.UpLeafInterleavedParameters
open DualTree.UpLeafInterleavedCanonical
open DualTree.UpLeafInterleavedGoodDecomposition
open DualTree.InterleavedFlatHalesJewett
open DualTree.ShiftedRaySlots

/-- The full Lemma-14 up-trace does not see ordinary D₀ substitutions,
so its canonicality implies exact D₀ parameter invariance on the
actual mixed span. Works even with nonempty D₂. -/
theorem plainInvariant_of_upCanonical
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ)
    (hcanonical : UpCanonical color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst)) :
    PlainInvariant kind (parameterColor hb kind w fallback color) := by
  intro σ τ a directions
  change color (parameterElement hb kind fallback
      (fun i => SpanAudit.eval (project w i) (σ i)) a directions) =
    color (parameterElement hb kind fallback
      (fun i => SpanAudit.eval (project w i) (τ i)) a directions)
  exact hcanonical
    (parameterElement_mem_span hb kind w fallback
      r hroot hfirst σ a directions)
    (parameterElement_mem_span hb kind w fallback
      r hroot hfirst τ a directions)
    ((parameterElement_sameUpTrace_iff hb kind fallback
      (fun i => SpanAudit.eval (project w i) (σ i))
      (fun i => SpanAudit.eval (project w i) (τ i))
      a a directions directions).2 ⟨rfl, by intro i; rfl⟩)

/-- Once Lemma-14 canonicality is known, the remaining two actual D₁
invariances suffice for Definition-11 Good, with no illicit step from
UpCanonical to either of those invariances. -/
theorem good_of_upCanonical_and_two_up_invariances
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ)
    (hcanonical : UpCanonical color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst))
    (hdirection : UpDirectionInvariant kind
      (parameterColor hb kind w fallback color))
    (hletter : UpLetterInvariant kind
      (parameterColor hb kind w fallback color)) :
    Good color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst) := by
  exact (good_iff_three_invariances hb kind w fallback
    r hroot hfirst color).2
      ⟨plainInvariant_of_upCanonical hb kind w fallback
          r hroot hfirst color hcanonical, hdirection, hletter⟩

/-- Exactly two new invariance obligations remain once UpCanonical
is already established. The forward implication does NOT assume
the two invariances; it derives them from actual Good. -/
theorem good_iff_two_up_invariances_of_upCanonical
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ)
    (hcanonical : UpCanonical color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst)) :
    Good color
        (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
          r hroot hfirst) ↔
      UpDirectionInvariant kind
          (parameterColor hb kind w fallback color) ∧
      UpLetterInvariant kind
          (parameterColor hb kind w fallback color) := by
  constructor
  · intro hgood
    have hthree := (good_iff_three_invariances hb kind w fallback
      r hroot hfirst color).1 hgood
    exact ⟨hthree.2.1, hthree.2.2⟩
  · rintro ⟨hdirection, hletter⟩
    exact good_of_upCanonical_and_two_up_invariances hb kind w fallback
      r hroot hfirst color hcanonical hdirection hletter


/-- For the exact no-D₂ hypothesis of the height-one Lemma 14,
UpCanonical is EQUIVALENT to uniformity in the ordinary Hales--Jewett
substitutions at fixed D₁ root letters and ambient directions. This
makes the precise established canonicalization input explicit. -/
theorem upCanonical_iff_plainInvariant_of_noBullet
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnb : NoBullet kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    UpCanonical color
        (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
          r hroot hfirst) ↔
      PlainInvariant kind
        (parameterColor hb kind w fallback color) := by
  constructor
  · intro hup
    exact plainInvariant_of_upCanonical hb kind w fallback
      r hroot hfirst color hup
  · intro huniform
    exact upCanonical_of_uniform_plain hb kind hnb w fallback
      r hroot hfirst color (by
        intro σ τ a directions
        exact huniform σ τ a directions)

end DualTree.UpLeafInterleavedGoodBridge
