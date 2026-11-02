import DualTree.PlainBlockBulletBlockSpan
import DualTree.ParameterVectorHalesJewett
import DualTree.MixedGood

/-!
# Genuine c-good Ramsey existence for p ordinary and q marked coordinates

This extends the already verified one-D₀/q-D₂ theorem to
an arbitrary finite block of p independent ordinary D₀
coordinates, followed by q independent D₂ marked coordinates,
still at intrinsic complete-skew height one.

A true finite parameter-uniform VECTOR Hales–Jewett theorem
selects synchronized variable positions in all p ordinary
coordinates while allowing different substitutions for each.
The parameter is the q-tuple of observed marked letters.
The genuine mixed word uses one EARLY ray support root
in every ordinary component and a separate LATER root in
every marked component, satisfying the full vector
1-complete-skew predicate and no fake D₁ leaves.

The verified mixed-span representation maps every actual
span element to those independent assignments. Hence
Definition-11 c-goodness follows without assuming a
pre-existing homogeneous mixed word.

No equality of colours across distinct D₂ tuples is asserted.
Higher intrinsic heights, D₁ up leaves, arbitrary kind
permutations and relative refinements remain open.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.FlatVectorHalesJewett

/-- Uniform finite-parametric vector colour constancy
implies c-goodness of the ACTUAL p-D₀/q-D₂ mixed word.
Only equal D₂ marked-letter tuples are compared. -/
theorem mixedWord_good_of_uniform_flat_vector
    {b N p q : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) (p + q) β (kind p q) → γ)
    (huniform :
      ∀ σ τ : Fin p → Fin 1 → β, ∀ a : Fin q → β,
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (σ i)) a) =
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (τ i)) a)) :
    Good color (mixedWord hb w fallback r hroot hfirst q) := by
  intro x y hx hy _ hletters
  obtain ⟨σ, a, hxrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst x hx
  obtain ⟨τ, a', hyrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst y hy
  have haeq : a = a' := by
    funext j
    let i : BulletIndex (kind p q) := bulletIndex p q j
    have h := hletters i
    rw [hxrepr, hyrepr] at h
    have hleft :=
      parameterElement_bullet_letter hb fallback
        (fun k => SpanAudit.eval (coordinateWord w k) (σ k)) a i
    have hright :=
      parameterElement_bullet_letter hb fallback
        (fun k => SpanAudit.eval (coordinateWord w k) (τ k)) a' i
    have hi : a (bulletCoordinate i) =
        a' (bulletCoordinate i) :=
      hleft.symm.trans (h.trans hright)
    change a (bulletCoordinate (bulletIndex p q j)) =
      a' (bulletCoordinate (bulletIndex p q j)) at hi
    simpa only [bulletCoordinate_bulletIndex] using hi
  calc
    color x =
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (σ i)) a) :=
      congrArg color hxrepr
    _ = color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (τ i)) a) :=
      huniform σ τ a
    _ = color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (τ i)) a') := by
      rw [haeq]
    _ = color y := (congrArg color hyrepr).symm

/-- Unconditional Definition-11 c-good finite mixed Ramsey
existence at intrinsic height one for p independent D₀
coordinates FOLLOWED BY q independently marked D₂
coordinates, with no D₁ coordinates.

Given a finite original alphabet with an explicit fallback
letter and any finite colour type, a finite ambient height
works uniformly for every colouring of the genuine mixed
product. No Good or monochromaticity assumption is passed.
The retained D₂ tuple may still affect the resulting colour.
-/
theorem exists_good_plainBlockBulletBlock_height_one
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) (p q : Nat) :
    ∃ n : Nat,
      ∀ color : Element b n (p + q) β (kind p q) → γ,
        ∃ f : MixedProduct.VariableWord b n (p + q) 1 β
            (SkewTree.forwardAuxB (b := b)) (kind p q),
          Good color f := by
  obtain ⟨N, hN⟩ :=
    ParameterVectorHalesJewett.exists_uniform_flat_vector_for_bullet_letters
      β γ p q 1
  refine ⟨N + 1, ?_⟩
  intro color
  let C : (Fin p → Fin N → β) → (Fin q → β) → γ :=
    fun u a => color (parameterElement hb fallback u a)
  obtain ⟨w, hproper, hconst⟩ := hN C
  obtain ⟨r, hroot, hfirst⟩ :=
    exists_first_variable_index w hproper
  refine ⟨mixedWord hb w fallback r hroot hfirst q, ?_⟩
  apply mixedWord_good_of_uniform_flat_vector
    hb w fallback r hroot hfirst color
  intro σ τ a
  exact hconst σ τ a

end DualTree.PlainBlockBulletBlock
