import DualTree.PlainBulletRayGeometry

/-!
# Exact parametrization of a true mixed D₀/D₂ span

This connects the separated-root geometry with the actual
Definition-11 mixed-product Element API. Every element of the
generated span is *completely specified* by:

  (1) an independent assignment to the one D₀ ray variable;
  (2) the independent β-letter observed at the fixed D₂ marker.

The tree word at the D₂ coordinate is fixed outside its marker;
the D₀ word is fixed outside the earlier ray slots. In particular
the D₀ letter at the D₂ marker is fixed, avoiding the obstruction
that would arise from using the same variable root for both.

This is a precise span representation, not a Ramsey existence
theorem. The next step applies finite-parameter Hales–Jewett
to these two independent coordinates.
-/

namespace DualTree.PlainBulletRay

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- An actual mixed element with a D₀ ray evaluation u and
a D₂ word determined by one independently chosen letter a.
No fake D₁ point is supplied. -/
noncomputable def parameterElement
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : β) :
    Element b (N + 1) 2 β kind where
  words := fun i =>
    if i = 0 then embedRay hb fallback u
    else endWordValue hb N fallback a
  upPoint := fun i => False.elim (noUp i)
  bulletPoint := fun _ => endRoot hb N

theorem parameterElement_zero
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : β) :
    (parameterElement hb fallback u a).words 0 =
      embedRay hb fallback u := by
  simp [parameterElement]

theorem parameterElement_one
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : β) :
    (parameterElement hb fallback u a).words 1 =
      endWordValue hb N fallback a := by
  simp [parameterElement]

/-- The retained D₂ observed letter of a parameter element
is exactly its explicitly supplied parameter a. -/
theorem parameterElement_marked_letter
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : β)
    (i : BulletIndex kind) :
    (parameterElement hb fallback u a).words i.1
      ((parameterElement hb fallback u a).bulletPoint i) = a := by
  have hi : i.1 = (1 : Fin 2) := bulletIndex_one i
  rw [hi]
  exact endWordValue_at_root hb fallback a

/-- Every point of this TRUE mixed-variable-word span has
the expected concrete two-parameter form. The chosen
D₀ flat word may have multiple occurrences of its one
variable, but its FIRST occurrence is the only support
root; the D₂ coordinate has its own LATER support root. -/
theorem span_element_eq_parameterElement
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) 2 β kind)
    (hx : x ∈ (twoRootMixedWord hb w fallback r hroot hfirst).span) :
    ∃ σ : Fin 1 → β, ∃ a : β,
      x = parameterElement hb fallback
        (SpanAudit.eval w σ) a := by
  have h0 :
      x.words 0 ∈
        (rayKVariableWord hb w fallback r hroot hfirst).span :=
    hx.1 0
  have h1 :
      x.words 1 ∈ (endKVariableWord hb N fallback).span :=
    hx.1 1
  obtain ⟨σ₀,hσ₀⟩ := h0
  obtain ⟨σ₁,hσ₁⟩ := h1
  let σ : Fin 1 → β := fun _ => σ₀ (rootVar hb r)
  let a : β := σ₁ (endVar hb N)
  have hw0 : x.words 0 =
      embedRay hb fallback (SpanAudit.eval w σ) := by
    calc
      x.words 0 =
          (rayKVariableWord hb w fallback r hroot hfirst).toVariableWord.eval σ₀ :=
        hσ₀.symm
      _ = embedRay hb fallback
          (SpanAudit.eval w (fun _ => σ₀ (rootVar hb r))) :=
        rayVariableWord_eval hb w fallback r hroot hfirst σ₀
      _ = embedRay hb fallback (SpanAudit.eval w σ) := rfl
  have hw1 : x.words 1 = endWordValue hb N fallback a := by
    calc
      x.words 1 = (endKVariableWord hb N fallback).toVariableWord.eval σ₁ :=
        hσ₁.symm
      _ = endWordValue hb N fallback (σ₁ (endVar hb N)) :=
        endVariableWord_eval hb fallback σ₁
      _ = endWordValue hb N fallback a := rfl
  have hwords : x.words =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).words := by
    funext i
    fin_cases i
    · exact hw0.trans
        (parameterElement_zero hb fallback (SpanAudit.eval w σ) a).symm
    · exact hw1.trans
        (parameterElement_one hb fallback (SpanAudit.eval w σ) a).symm
  have hup : x.upPoint =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).upPoint := by
    funext i
    exact False.elim (noUp i)
  have hbullet : x.bulletPoint =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).bulletPoint := by
    funext i
    exact bulletPoint_eq_endRoot hb w fallback r hroot hfirst
      x hx i
  refine ⟨σ, a, ?_⟩
  cases x with
  | mk words upPoint bulletPoint =>
    change words = _ at hwords
    change upPoint = _ at hup
    change bulletPoint = _ at hbullet
    cases hwords
    cases hup
    cases hbullet
    rfl

end DualTree.PlainBulletRay
