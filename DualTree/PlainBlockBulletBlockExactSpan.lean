import DualTree.PlainBlockBulletBlockRamsey
import DualTree.PlainBulletBlockExactSpan

/-!
# Converse span and nonvacuity for p ordinary / q marked coordinates

The p-D₀/q-D₂ height-one c-good existence theorem must not be read as a
vacuous statement about a possibly empty mixed span.  This module proves
the converse to `span_element_eq_parameterElement`: each tuple of p
independently chosen flat variable values and each q-tuple of independently
chosen D₂ letters produces an element of the ACTUAL
`MixedProduct.VariableWord.span`.

The result identifies the complete span, including p=0 and q=0, and
produces a point from the explicit fallback alphabet letter.  It does not
assert D₁ or higher-height Ramsey existence.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay
open DualTree.FlatVectorHalesJewett

/-- All p ordinary substitutions and q marked letters really occur in
the mixed-product span, without coupling their choices. -/
theorem parameterElement_mem_span
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : Fin p → Fin 1 → β) (a : Fin q → β) :
    parameterElement hb fallback
        (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a ∈
      (mixedWord hb w fallback r hroot hfirst q).span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < p
    · let j : Fin p := plainCoordinate i hi
      let τ :
          (DualTree.VectorRayHalesJewett.coordinateRayWord
            hb w fallback r hroot hfirst j).Vars → β :=
        fun _ => σ j 0
      have hσ : (fun _ : Fin 1 => τ (rootVar hb r)) = σ j := by
        funext v
        have hv : v = 0 := Fin.eq_zero v
        subst v
        rfl
      have heval :
          (DualTree.VectorRayHalesJewett.coordinateRayWord
            hb w fallback r hroot hfirst j).toVariableWord.eval τ =
          embedRay hb fallback
            (SpanAudit.eval (coordinateWord w j) (σ j)) := by
        simpa only [hσ] using
          (DualTree.VectorRayHalesJewett.coordinateRayWord_eval
            hb w fallback r hroot hfirst j τ)
      have hmem :
          embedRay hb fallback
              (SpanAudit.eval (coordinateWord w j) (σ j)) ∈
            (DualTree.VectorRayHalesJewett.coordinateRayWord
              hb w fallback r hroot hfirst j).span :=
        ⟨τ, heval⟩
      simpa [mixedWord, vectorWord, parameterElement, hi,
        j, plainCoordinate] using hmem
    · let bi : BulletIndex (kind p q) :=
        ⟨i, by simp [kind, hi]⟩
      let τ : (endKVariableWord hb N fallback).Vars → β :=
        fun _ => a (bulletCoordinate bi)
      have heval :
          (endKVariableWord hb N fallback).toVariableWord.eval τ =
            endWordValue hb N fallback (a (bulletCoordinate bi)) := by
        have h := endVariableWord_eval (N := N) hb fallback τ
        change (endVariableWord hb N fallback).eval τ =
          endWordValue hb N fallback (a (bulletCoordinate bi))
        simpa [τ] using h
      have hmem :
          endWordValue hb N fallback (a (bulletCoordinate bi)) ∈
            (endKVariableWord hb N fallback).span :=
        ⟨τ, heval⟩
      simpa [mixedWord, vectorWord, parameterElement, hi, bi] using hmem
  · intro i
    exact False.elim (noUp i)
  · intro i
    have hi : ¬ i.1.val < p := not_lt.mpr (bullet_ge_plain i)
    have hmem :
        endRoot hb N ∈ (endKVariableWord hb N fallback).support := by
      change endRoot hb N ∈ [endRoot hb N]
      simp
    simpa [mixedWord, vectorWord, parameterElement, hi] using hmem

/-- The genuine mixed span is EXACTLY the full independent parameter
family, not just contained in it. -/
theorem mixedWord_span_eq_parameter_range
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (mixedWord hb w fallback r hroot hfirst q).span =
      Set.range (fun z : (Fin p → Fin 1 → β) × (Fin q → β) =>
        parameterElement hb fallback
          (fun j => SpanAudit.eval (coordinateWord w j) (z.1 j))
          z.2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, a, heq⟩ :=
      span_element_eq_parameterElement
        hb w fallback r hroot hfirst x hx
    exact ⟨⟨σ, a⟩, heq.symm⟩
  · rintro ⟨⟨σ, a⟩, rfl⟩
    exact parameterElement_mem_span
      hb w fallback r hroot hfirst σ a

/-- An explicit inhabitant rules out vacuous c-goodness from an empty
mixed span, uniformly in p and q. -/
theorem mixedWord_span_nonempty
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    ((mixedWord hb w fallback r hroot hfirst q).span).Nonempty := by
  let σ : Fin p → Fin 1 → β := fun _ _ => fallback
  let a : Fin q → β := fun _ => fallback
  exact ⟨parameterElement hb fallback
      (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a,
    parameterElement_mem_span hb w fallback r hroot hfirst σ a⟩

end DualTree.PlainBlockBulletBlock
