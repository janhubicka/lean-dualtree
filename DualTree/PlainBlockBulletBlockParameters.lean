import DualTree.PlainBlockBulletBlockGeometry
import DualTree.PlainBulletBlockSpan

/-!
# Actual parameter elements for p ordinary and q marked coordinates

Given a synchronized flat vector word on p independent D₀
coordinates and a tuple of q D₂ marked letters, form an
ACTUAL source-facing MixedProduct.Element. All p ordinary
words are embedded on the first N ray slots; each D₂ word
is fixed outside its later marked root and receives its
own independent letter there.

We prove the relevant exact Fin(p+q) index conversions,
the observed D₂ letter formula and fixed bullet markers
on a genuine generated mixed span. This is preparation
for a fully general p-D₀/q-D₂ height-one Ramsey theorem;
it does not itself assert colour canonization.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay

/-- Embed an actual D₀ coordinate into the first p slots
of the mixed array Fin(p+q). -/
def plainIndex (p q : Nat) (j : Fin p) : Fin (p + q) :=
  ⟨j.val, by omega⟩

/-- Recover the D₀ index from a mixed index satisfying
the plain-coordinate bound. -/
def plainCoordinate {p q : Nat}
    (i : Fin (p + q)) (hi : i.val < p) : Fin p :=
  ⟨i.val, hi⟩

theorem plainIndex_plainCoordinate
    {p q : Nat} (i : Fin (p + q)) (hi : i.val < p) :
    plainIndex p q (plainCoordinate i hi) = i := by
  apply Fin.ext
  rfl

/-- A genuine D₂ coordinate comes from exactly one
independent retained-letter index in Fin q. -/
theorem bulletIndex_bulletCoordinate
    {p q : Nat} (i : BulletIndex (kind p q)) :
    (bulletIndex p q (bulletCoordinate i)).1 = i.1 := by
  apply Fin.ext
  have hge : p ≤ i.1.val := bullet_ge_plain i
  simp only [bulletIndex, bulletCoordinate]
  omega

/-- Actual source-facing mixed element, with independently
assigned original words on p ordinary coordinates and
independent marked letters in q D₂ coordinates. -/
noncomputable def parameterElement
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin p → Fin N → β) (a : Fin q → β) :
    Element b (N + 1) (p + q) β (kind p q) where
  words := fun i =>
    if hi : i.val < p then
      embedRay hb fallback (u (plainCoordinate i hi))
    else
      endWordValue hb N fallback
        (a (bulletCoordinate
          ⟨i, by simp [kind, hi]⟩))
  upPoint := fun i => False.elim (noUp i)
  bulletPoint := fun _ => endRoot hb N

/-- Every ordinary coordinate is exactly the embedding
of its supplied independent flat vector word. -/
theorem parameterElement_plain
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin p → Fin N → β) (a : Fin q → β)
    (j : Fin p) :
    (parameterElement hb fallback u a).words
        (plainIndex p q j) =
      embedRay hb fallback (u j) := by
  have hj : (plainIndex p q j).val < p := j.isLt
  simp [parameterElement, hj, plainIndex, plainCoordinate]

/-- Each genuine D₂ observation is exactly the selected
parameter at its source-facing BulletIndex coordinate. -/
theorem parameterElement_bullet_letter
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin p → Fin N → β) (a : Fin q → β)
    (i : BulletIndex (kind p q)) :
    (parameterElement hb fallback u a).words i.1
      ((parameterElement hb fallback u a).bulletPoint i) =
        a (bulletCoordinate i) := by
  have hi : ¬i.1.val < p := not_lt.mpr (bullet_ge_plain i)
  simp [parameterElement, hi, endWordValue]

/-- Actual D₂ marker points in the generated mixed span
are the fixed later root, independent of all D₀ and D₂
variable evaluations. -/
theorem bulletPoint_eq_endRoot
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) (p + q) β (kind p q))
    (hx : x ∈ (mixedWord hb w fallback r hroot hfirst q).span)
    (i : BulletIndex (kind p q)) :
    x.bulletPoint i = endRoot hb N := by
  have hi : ¬i.1.val < p :=
    not_lt.mpr (bullet_ge_plain i)
  have h := hx.2.2 i
  have hmem :
      x.bulletPoint i ∈ (endKVariableWord hb N fallback).support := by
    simpa [mixedWord, vectorWord, hi] using h
  change x.bulletPoint i ∈ [endRoot hb N] at hmem
  simpa using hmem

end DualTree.PlainBlockBulletBlock
