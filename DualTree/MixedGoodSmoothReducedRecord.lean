import DualTree.MixedGoodSmoothGamma2Erasure

/-!
# The canonical residual bullet record of a smooth c-good colouring

Definition 11's c-goodness allows every D₂ letter and marked point.
Definition 21 smoothness, however, makes the letter at a Γ₂
marked point irrelevant. The preceding proof changes one actual
local variable assignment within the original mixed span to erase
a single Γ₂ letter while holding its full outside-cone word fixed.

Here all Γ₂ marked letters are normalized SIMULTANEOUSLY to one
arbitrary fallback letter. Each coordinate is adjusted by the same
verified one-variable reassignment, using only that component's
own source-variable support. The normalized element remains
in the genuine mixed-product span and is smooth-related to
the original.

Thus a colouring that is both c-good on f and globally smooth
factors through the REDUCED bullet record consisting of:
- every D₂ marked point;
- observed letters ONLY for Γ₁ D₂ indices.

No starred-span monochromaticity or equality of unrestricted
word coordinates is asserted. Elimination of the remaining
Γ₁ letters and Γ₂ marker points is a separate Ramsey step.
-/

namespace DualTree.MixedProduct

/-- Normalize exactly the letters observed at Γ₂ selected
markers, changing only the corresponding actual support-root
variable. Γ₁ words and all nonbullet coordinates remain intact. -/
noncomputable def normalizeGamma2Letters
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β) :
    Element b n d β kind := by
  classical
  exact {
    words := fun j =>
      if hk : kind j = CoordKind.bullet then
        if gamma1 (⟨j,hk⟩ : BulletIndex kind) then
          x.words j
        else
          (reassignMarkedLetter f x hx ⟨j,hk⟩ fallback).words j
      else x.words j
    upPoint := x.upPoint
    bulletPoint := x.bulletPoint
  }

/-- The normalization is an actual point of the original
mixed-variable-word span, not a freely patched outside-span
word. Every component either keeps its current evaluated
word or changes exactly one genuine local variable value. -/
theorem normalizeGamma2Letters_mem_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β) :
    normalizeGamma2Letters f x hx gamma1 fallback ∈ f.span := by
  classical
  refine ⟨?_, hx.2.1, hx.2.2⟩
  intro j
  by_cases hk : kind j = CoordKind.bullet
  · let i : BulletIndex kind := ⟨j, hk⟩
    cases hg : gamma1 i with
    | true =>
        simpa [normalizeGamma2Letters, hk, i, hg] using hx.1 j
    | false =>
        have h := (reassignMarkedLetter_mem_span
          f x hx i fallback).1 j
        simpa [normalizeGamma2Letters, hk, i, hg] using h
  · simpa [normalizeGamma2Letters, hk] using hx.1 j

/-- Every selected D₂ point remains literally unchanged. -/
theorem normalizeGamma2Letters_bulletPoint
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β)
    (i : BulletIndex kind) :
    (normalizeGamma2Letters f x hx gamma1 fallback).bulletPoint i =
      x.bulletPoint i := rfl

/-- In Γ₁ the old marked letter survives; in Γ₂ the
new observed marked letter is exactly the selected fallback. -/
theorem normalizeGamma2Letters_at_bullet
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β)
    (i : BulletIndex kind) :
    (normalizeGamma2Letters f x hx gamma1 fallback).words
        i.1 (x.bulletPoint i) =
      if gamma1 i then x.words i.1 (x.bulletPoint i)
      else fallback := by
  classical
  cases hg : gamma1 i with
  | true =>
      simp [normalizeGamma2Letters, i.2, hg]
  | false =>
      have h := reassignMarkedLetter_at_mark f x hx i fallback
      simpa [normalizeGamma2Letters, i.2, hg] using h

/-- The entire normalization is Γ₁/Γ₂ SMOOTH-RELATED
to the original point, since all Γ₁ words remain fixed
and every Γ₂ word changes only at its selected marked
root variable, never outside that root's inclusive cone. -/
theorem normalizeGamma2Letters_smooth
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β) :
    SmoothRelated gamma1 x
      (normalizeGamma2Letters f x hx gamma1 fallback) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hk : ¬ kind j = CoordKind.bullet := hj
    simp [normalizeGamma2Letters, hk]
  · intro j
    rfl
  · intro i
    cases hg : gamma1 i with
    | true =>
        change x.words i.1 =
          (normalizeGamma2Letters f x hx gamma1 fallback).words i.1
        simp [normalizeGamma2Letters, i.2, hg]
    | false =>
        change x.bulletPoint i =
          (normalizeGamma2Letters f x hx gamma1 fallback).bulletPoint i ∧
          ∀ t : BoundedNode b n,
            ¬ IsPrefix (x.bulletPoint i).1 t.1 →
            x.words i.1 t =
              (normalizeGamma2Letters f x hx gamma1 fallback).words i.1 t
        refine ⟨rfl, ?_⟩
        intro t ht
        have hword :
            (normalizeGamma2Letters f x hx gamma1 fallback).words i.1 t =
              (reassignMarkedLetter f x hx i fallback).words i.1 t := by
          simp [normalizeGamma2Letters, i.2, hg]
        rw [hword]
        exact (reassignMarkedLetter_outside_cone
          f x hx i fallback t ht).symm

/-- Complete mixed-product reduced-record factorization:
if a colouring is c-good on f and smooth for gamma1,
two elements of f.span have equal colours whenever all
marked D₂ points agree and the observed D₂ letters agree
only on Γ₁. The Γ₂ letters need NOT agree.

The proof normalizes all Γ₂ letters to the SAME fallback
and uses genuine span membership, smoothness and c-goodness.
No full starred-span monochromaticity is assumed. -/
theorem good_smooth_color_eq_of_reduced_bullet_record
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hpoints : ∀ i : BulletIndex kind,
      x.bulletPoint i = y.bulletPoint i)
    (hgamma1 : ∀ i : BulletIndex kind,
      gamma1 i = true →
      x.words i.1 (x.bulletPoint i) =
        y.words i.1 (y.bulletPoint i)) :
    c x = c y := by
  classical
  let X := normalizeGamma2Letters f x hx gamma1 fallback
  let Y := normalizeGamma2Letters f y hy gamma1 fallback
  have hXspan : X ∈ f.span :=
    normalizeGamma2Letters_mem_span f x hx gamma1 fallback
  have hYspan : Y ∈ f.span :=
    normalizeGamma2Letters_mem_span f y hy gamma1 fallback
  have hXsm : SmoothRelated gamma1 x X :=
    normalizeGamma2Letters_smooth f x hx gamma1 fallback
  have hYsm : SmoothRelated gamma1 y Y :=
    normalizeGamma2Letters_smooth f y hy gamma1 fallback
  have hmarks : ∀ i : BulletIndex kind,
      X.bulletPoint i = Y.bulletPoint i := by
    intro i
    exact hpoints i
  have hletters : ∀ i : BulletIndex kind,
      X.words i.1 (X.bulletPoint i) =
        Y.words i.1 (Y.bulletPoint i) := by
    intro i
    change
      (normalizeGamma2Letters f x hx gamma1 fallback).words
        i.1 (x.bulletPoint i) =
      (normalizeGamma2Letters f y hy gamma1 fallback).words
        i.1 (y.bulletPoint i)
    rw [normalizeGamma2Letters_at_bullet,
      normalizeGamma2Letters_at_bullet]
    cases hg : gamma1 i with
    | true => simpa [hg] using hgamma1 i hg
    | false => simp [hg]
  calc
    c x = c X := hsmooth x X hXsm
    _ = c Y := hgood hXspan hYspan hmarks hletters
    _ = c y := (hsmooth y Y hYsm).symm

end DualTree.MixedProduct
