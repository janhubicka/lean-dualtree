import DualTree.PlainBulletRaySpan
import DualTree.ParameterHalesJewett
import DualTree.MixedGood

/-!
# Genuine mixed D₀/D₂ c-good Ramsey existence, intrinsic height ONE

This is the first simultaneous, nontrivial D₀ ∪ D₂ case of
Definition 11's mixed-product Ramsey problem, with no D₁ coordinates.

The D₀ variable word uses the first N ray slots; the single D₂
variable root and marked point is the NEXT ray node at level N.
Both supports are genuine singleton 1-complete-skew subtrees
and their vector support satisfies the full cross-coordinate
length-ordering clause. The D₂ root is strictly after every D₀
variable occurrence.

Given any finite colouring of ACTUAL mixed-product elements,
define a flat colouring C(u)(a) by inserting D₀ tree word u
and D₂ marker letter a into the real mixed-product Element.
The verified uniform finite-parameter Hales–Jewett theorem
produces a genuine flat D₀ line with the SAME colour for all
its assignments, separately at EACH D₂ letter a. The exact
mixed-span representation theorem then proves Definition-11
c-goodness, preserving all permitted dependence on D₂ letters.

This is UNCONDITIONAL finite c-good mixed Ramsey existence
for the coordinate-kind tuple (D₀,D₂) at intrinsic dimension 1.
It is not full starred-span monochromaticity and it does not
cover arbitrary partitions, D₁ leaves, higher complete-skew
dimensions or the manuscript's quantitative Corollary 22.
-/

namespace DualTree.PlainBulletRay

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- The unique D₂ index, identified as an actual BulletIndex
of the source-facing kind function, not a synthetic marker. -/
def bulletIndex : BulletIndex kind :=
  ⟨1, by simp [kind]⟩

/-- The distinguished marked letter of a genuine parametrized
mixed element is its independent parameter a. -/
theorem parameterElement_bulletIndex_letter
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : β) :
    (parameterElement hb fallback u a).words bulletIndex.1
      ((parameterElement hb fallback u a).bulletPoint bulletIndex) = a :=
  parameterElement_marked_letter hb fallback u a bulletIndex

/-- The true source-facing Definition-11 c-good conclusion
for the separated-root D₀/D₂ mixed word follows from the
FLAT Hales–Jewett parametric colour constancy, with NO
additional equality requirement on the D₂ letter parameter.
The true marked point is fixed by the support. -/
theorem twoRootMixedWord_good_of_uniform_flat
    {b N : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) 2 β kind → γ)
    (huniform : ∀ σ τ : Fin 1 → β, ∀ a : β,
      color (parameterElement hb fallback (SpanAudit.eval w σ) a) =
        color (parameterElement hb fallback (SpanAudit.eval w τ) a)) :
    Good color (twoRootMixedWord hb w fallback r hroot hfirst) := by
  intro x y hx hy _ hletters
  obtain ⟨σ, a, hxrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst x hx
  obtain ⟨τ, a', hyrepr⟩ :=
    span_element_eq_parameterElement
      hb w fallback r hroot hfirst y hy
  have heq : a = a' := by
    have h := hletters bulletIndex
    rw [hxrepr, hyrepr] at h
    simpa only [parameterElement_bulletIndex_letter]
      using h
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

/-- UNCONDITIONAL finite c-good Ramsey existence for an actual
mixed product with one D₀ coordinate AND one D₂ coordinate,
D₁ empty, and intrinsic complete-skew height one.

No Ramsey word f, monotonicity or goodness is passed as
an assumption. Every finite colouring is handled at some
finite ambient tree height depending only on β, γ.
The D₂ observed root letter may still affect the colour;
monochromaticity of the whole mixed span is NOT concluded. -/
theorem exists_good_plainBullet_height_one
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) :
    ∃ n : Nat,
      ∀ color : Element b n 2 β kind → γ,
        ∃ f : MixedProduct.VariableWord b n 2 1 β
            (SkewTree.forwardAuxB (b := b)) kind,
          Good color f := by
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_one_variable_uniform_in_bullet_letter
      β γ
  refine ⟨N + 1, ?_⟩
  intro color
  let C : (Fin N → β) → β → γ :=
    fun u a => color (parameterElement hb fallback u a)
  obtain ⟨w, ⟨j, hj⟩, hconst⟩ := hN C
  have hproper : ∀ v : Fin 1, ∃ i : Fin N, w i = Sum.inr v := by
    intro v
    have hv : v = 0 := Fin.eq_zero v
    subst v
    exact ⟨j, hj⟩
  obtain ⟨r, hroot, hfirst⟩ :=
    exists_first_variable_index w hproper
  refine ⟨twoRootMixedWord hb w fallback r hroot hfirst, ?_⟩
  apply twoRootMixedWord_good_of_uniform_flat
    hb w fallback r hroot hfirst color
  intro σ τ a
  exact hconst σ τ a

end DualTree.PlainBulletRay
