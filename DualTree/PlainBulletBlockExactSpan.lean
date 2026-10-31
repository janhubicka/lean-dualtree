import DualTree.PlainBulletBlockRamsey

/-!
# Exact, nonvacuous mixed span with q independent D₂ letters

The unconditional one-D₀/q-D₂ c-good Ramsey existence theorem
uses a genuine finite-parameter representation of every mixed-span
point. For adversarial completeness we prove the CONVERSE too:
every ordinary Hales–Jewett variable assignment and every
INDEPENDENT q-tuple of D₂ observed letters is really attained
by an element of the source-facing mixed span.

Thus the span is precisely the full parameterized family,
not a proper or potentially empty subset. In particular
the D₂ coordinates can vary independently at their common
GEOMETRIC marked root because their word variables live in
different vector components.
-/

namespace DualTree.PlainBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay

/-- Every D₀ substitution together with every q-tuple of
D₂ marked letters gives a GENUINE element in the actual
mixed-variable-word span. -/
theorem parameterElement_mem_span
    {b N q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : Fin 1 → β) (a : Fin q → β) :
    parameterElement hb fallback (SpanAudit.eval w σ) a ∈
      (mixedWord hb w fallback r hroot hfirst q).span := by
  let τ₀ :
      (rayKVariableWord hb w fallback r hroot hfirst).Vars → β :=
    fun _ => σ 0
  have heval₀ :
      (rayKVariableWord hb w fallback r hroot hfirst).toVariableWord.eval τ₀ =
        embedRay hb fallback (SpanAudit.eval w σ) := by
    have h := rayVariableWord_eval hb w fallback r hroot hfirst τ₀
    have hσ : (fun _ : Fin 1 => τ₀ (rootVar hb r)) = σ := by
      funext j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
    change (rayVariableWord hb w fallback r hroot hfirst).eval τ₀ =
      embedRay hb fallback (SpanAudit.eval w σ)
    simpa only [hσ] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = (0 : Fin (q + 1))
    · subst i
      have hmem : embedRay hb fallback (SpanAudit.eval w σ) ∈
          (rayKVariableWord hb w fallback r hroot hfirst).span :=
        ⟨τ₀, heval₀⟩
      simpa [mixedWord, vectorWord, parameterElement] using hmem
    · let bi : BulletIndex (kind q) :=
        ⟨i, by simp [kind, hi]⟩
      let τ : (endKVariableWord hb N fallback).Vars → β :=
        fun _ => a (bulletCoordinate bi)
      have heval :
          (endKVariableWord hb N fallback).toVariableWord.eval τ =
            endWordValue hb N fallback (a (bulletCoordinate bi)) := by
        have h := endVariableWord_eval (N := N) hb fallback τ
        simpa [τ] using h
      have hmem :
          endWordValue hb N fallback (a (bulletCoordinate bi)) ∈
          (endKVariableWord hb N fallback).span :=
        ⟨τ, heval⟩
      simpa [mixedWord, vectorWord, parameterElement, hi, bi] using hmem
  · intro i
    exact False.elim (noUp i)
  · intro i
    have hi := bullet_ne_zero i
    have hmem :
        endRoot hb N ∈ (endKVariableWord hb N fallback).support := by
      change endRoot hb N ∈ [endRoot hb N]
      simp
    simpa [mixedWord, vectorWord, parameterElement, hi] using hmem

/-- The ACTUAL mixed span is EXACTLY the full set of
independently assigned D₀ Hales–Jewett variables and q
D₂ marker letters, with no hidden restriction on the
allowed D₂ tuples or their common geometric root. -/
theorem mixedWord_span_eq_parameter_range
    {b N q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (mixedWord hb w fallback r hroot hfirst q).span =
      Set.range (fun p : (Fin 1 → β) × (Fin q → β) =>
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

/-- In particular the genuine mixed span is nonempty
for every q when a fallback alphabet letter is supplied. -/
theorem mixedWord_span_nonempty
    {b N q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    ((mixedWord hb w fallback r hroot hfirst q).span).Nonempty := by
  let σ : Fin 1 → β := fun _ => fallback
  let a : Fin q → β := fun _ => fallback
  exact ⟨parameterElement hb fallback (SpanAudit.eval w σ) a,
    parameterElement_mem_span hb w fallback r hroot hfirst σ a⟩

end DualTree.PlainBulletBlock
