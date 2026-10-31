import DualTree.PlainBulletBlockSpan
import DualTree.ParameterHalesJewett
import DualTree.MixedGood

/-!
# Genuine mixed Ramsey existence: one D₀ and q independent D₂ markers

Generalize the verified two-coordinate D₀/D₂ c-good theorem to an
arbitrary finite tuple of q D₂ coordinates following one ordinary D₀
coordinate in the mixed coordinate order.

The single D₀ variable root occurs at the first Hales–Jewett
variable position on a fixed ray. Every D₂ component has its OWN
independent word variable, at the common LATER geometric root.
Distinct coordinate words can evaluate these variables to unrelated
letters despite sharing the same geometric root.

Apply finite-parameter Hales–Jewett with parameter type
Fin q → β, rather than incorrectly claiming D₂ letters or
Γ₁ residual records become constant. The genuine mixed span
representation converts parameter-uniformity to Definition-11
c-goodness in the ACTUAL MixedProduct.VariableWord API.

No selected c-good mixed word is assumed. D₁ up-leaf selection,
multiple ordinary coordinates, higher intrinsic heights, and
the quantitative Corollary 22 remain open.
-/

namespace DualTree.PlainBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- Parametric Hales–Jewett constancy for each retained
tuple of observed D₂ letters gives c-goodness on the true
q-marked mixed span. Equality of the parameter tuples is
deduced from the marked-letter observations in the exact
Definition-11 Good hypothesis. -/
theorem mixedWord_good_of_uniform_flat
    {b N q : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) (q + 1) β (kind q) → γ)
    (huniform : ∀ σ τ : Fin 1 → β, ∀ a : Fin q → β,
      color (parameterElement hb fallback (SpanAudit.eval w σ) a) =
        color (parameterElement hb fallback (SpanAudit.eval w τ) a)) :
    Good color (mixedWord hb w fallback r hroot hfirst q) := by
  intro x y hx hy _ hletters
  obtain ⟨σ, a, hxrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst x hx
  obtain ⟨τ, a', hyrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst y hy
  have heq : a = a' := by
    funext j
    let i : BulletIndex (kind q) := bulletIndex q j
    have h := hletters i
    rw [hxrepr, hyrepr] at h
    have ha := parameterElement_bullet_letter
      hb fallback (SpanAudit.eval w σ) a i
    have hb' := parameterElement_bullet_letter
      hb fallback (SpanAudit.eval w τ) a' i
    have hi : a (bulletCoordinate i) =
        a' (bulletCoordinate i) :=
      ha.symm.trans (h.trans hb')
    simpa only [bulletCoordinate_bulletIndex] using hi
  calc
    color x =
        color (parameterElement hb fallback
          (SpanAudit.eval w σ) a) :=
      congrArg color hxrepr
    _ = color (parameterElement hb fallback
          (SpanAudit.eval w τ) a) :=
      huniform σ τ a
    _ = color (parameterElement hb fallback
          (SpanAudit.eval w τ) a') := by rw [heq]
    _ = color y := (congrArg color hyrepr).symm

/-- UNCONDITIONAL genuine mixed-product c-good Ramsey
existence at intrinsic complete-skew height one, for
ONE ordinary D₀ coordinate followed by ANY finite
number q of independent marked D₂ coordinates, D₁ empty.

The proof constructs a finite ambient height n and a
true mixed variable word for EVERY finite colouring.
The retained D₂ marker tuple may influence the colour,
so monochromaticity of the full span is not asserted. -/
theorem exists_good_plainBulletBlock_height_one
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) (q : Nat) :
    ∃ n : Nat,
      ∀ color : Element b n (q + 1) β (kind q) → γ,
        ∃ f : MixedProduct.VariableWord b n (q + 1) 1 β
            (SkewTree.forwardAuxB (b := b)) (kind q),
          Good color f := by
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_uniform_flat_fibre_constancy
      β (Fin q → β) γ 1
  refine ⟨N + 1, ?_⟩
  intro color
  let C : (Fin N → β) → (Fin q → β) → γ :=
    fun u a => color (parameterElement hb fallback u a)
  obtain ⟨w, hproper, hconst⟩ := hN C
  obtain ⟨r, hroot, hfirst⟩ :=
    exists_first_variable_index w hproper
  refine ⟨mixedWord hb w fallback r hroot hfirst q, ?_⟩
  apply mixedWord_good_of_uniform_flat
    hb w fallback r hroot hfirst color
  intro σ τ a
  exact hconst σ τ a

end DualTree.PlainBulletBlock
