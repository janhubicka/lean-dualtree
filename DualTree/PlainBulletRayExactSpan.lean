import DualTree.PlainBulletRayRamsey

/-!
# The genuine D₀/D₂ mixed Ramsey span is EXACTLY the parameter family

The positive c-good theorem uses the fact that every actual
mixed-span element is parametrized by one D₀ Hales–Jewett assignment
and one independently retained D₂ marker letter. To exclude a
potential vacuity trap, we now verify the REVERSE inclusion too:
every pair of parameters is actually realized in the source-facing
MixedProduct.VariableWord.span, with the correct tree-word evaluations
and D₂ marker support membership.

Thus the mixed span equals the full two-parameter family, not just
a subset of it. In particular it is nonempty and the free D₂
letter can be evaluated independently of the D₀ variable.
-/

namespace DualTree.PlainBulletRay

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- Every D₀ variable assignment and every independent D₂
marked-root letter are simultaneously realizable by a
GENUINE element of the two-root mixed-product span. This
is the converse of span_element_eq_parameterElement. -/
theorem parameterElement_mem_span
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : Fin 1 → β) (a : β) :
    parameterElement hb fallback (SpanAudit.eval w σ) a ∈
      (twoRootMixedWord hb w fallback r hroot hfirst).span := by
  let τ₀ : (rayKVariableWord hb w fallback r hroot hfirst).Vars → β :=
    fun _ => σ 0
  have heval₀ :
      (rayKVariableWord hb w fallback r hroot hfirst).toVariableWord.eval τ₀ =
        embedRay hb fallback (SpanAudit.eval w σ) := by
    have h := rayVariableWord_eval hb w fallback r hroot hfirst τ₀
    have hσ : (fun _ : Fin 1 => τ₀ (rootVar hb r)) = σ := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    simpa only [hσ] using h
  let τ₁ : (endKVariableWord hb N fallback).Vars → β :=
    fun _ => a
  have heval₁ :
      (endKVariableWord hb N fallback).toVariableWord.eval τ₁ =
        endWordValue hb N fallback a := by
    have h := endVariableWord_eval (N := N) hb fallback τ₁
    simpa only using h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = (0 : Fin 2)
    · subst i
      change embedRay hb fallback (SpanAudit.eval w σ) ∈
        (rayKVariableWord hb w fallback r hroot hfirst).span
      exact ⟨τ₀, heval₀⟩
    · have h1 : i = (1 : Fin 2) := by
        apply Fin.ext
        have hlt : i.val < 2 := i.isLt
        have hpos : i.val ≠ 0 := by
          intro hz
          apply hi
          apply Fin.ext
          exact hz
        omega
      subst i
      change endWordValue hb N fallback a ∈
        (endKVariableWord hb N fallback).span
      exact ⟨τ₁, heval₁⟩
  · intro i
    exact False.elim (noUp i)
  · intro i
    rw [bulletIndex_one i]
    change endRoot hb N ∈ [endRoot hb N]
    simp

/-- Exact equality of the ACTUAL mixed span and the entire
two-parameter family, with independent original alphabet
D₀ and D₂ assignments. No artificial restriction to a
smaller choice of target input points survives. -/
theorem twoRootMixedWord_span_eq_parameter_range
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (twoRootMixedWord hb w fallback r hroot hfirst).span =
      Set.range (fun p : (Fin 1 → β) × β =>
        parameterElement hb fallback
          (SpanAudit.eval w p.1) p.2) := by
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

/-- The c-good existence result is not vacuous: the constructed
mixed variable word has a genuine element in its span for
every source alphabet containing the chosen fallback letter. -/
theorem twoRootMixedWord_span_nonempty
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    ((twoRootMixedWord hb w fallback r hroot hfirst).span).Nonempty := by
  let σ : Fin 1 → β := fun _ => fallback
  exact ⟨parameterElement hb fallback (SpanAudit.eval w σ) fallback,
    parameterElement_mem_span hb w fallback r hroot hfirst σ fallback⟩

end DualTree.PlainBulletRay
