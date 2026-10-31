import DualTree.PlainBulletBlockGeometry
import DualTree.PlainBulletRaySpan

/-!
# Exact mixed span for one D₀ coordinate and q independent D₂ markers

The source-facing mixed variable word has one early root-aligned
ordinary variable on a ray and q independently evaluable D₂ word
variables at a later root (one variable in EACH component).
The D₂ variables share their GEOMETRIC node but not their
substitution values; this is allowed by full vector 1-completeness.

We establish that its entire actual mixed span consists EXACTLY
of pairs: (an evaluated one-variable D₀ Hales–Jewett word,
a vector of q independently selected D₂ marked letters).

This representation is a substantive coverage theorem, not a
placeholder assumption about the span. Its purpose is to allow
the verified uniform Hales–Jewett theorem with finite parameter
type (Fin q → β) to yield a true q-marker c-good mixed word.
-/

namespace DualTree.PlainBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay

/-- Every genuine D₂ coordinate is the successor of its
own Fin q marker index. -/
theorem succ_bulletCoordinate
    {q : Nat} (i : BulletIndex (kind q)) :
    Fin.succ (bulletCoordinate i) = i.1 := by
  apply Fin.ext
  have hne : i.1.val ≠ 0 := by
    intro hz
    apply bullet_ne_zero i
    apply Fin.ext
    exact hz
  have hlt : i.1.val < q + 1 := i.1.isLt
  simp only [bulletCoordinate, Fin.val_succ]
  omega

/-- The D₂ coordinates of the actual mixed element are
parametrized by a tuple of independent letters, without
introducing any fictional D₁/up points. -/
noncomputable def parameterElement
    {b N q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : Fin q → β) :
    Element b (N + 1) (q + 1) β (kind q) where
  words := fun i =>
    if hi : i = 0 then embedRay hb fallback u
    else endWordValue hb N fallback
      (a (bulletCoordinate
        ⟨i, by simp [kind, hi]⟩))
  upPoint := fun i => False.elim (noUp i)
  bulletPoint := fun _ => endRoot hb N

theorem parameterElement_plain
    {b N q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : Fin q → β) :
    (parameterElement hb fallback u a).words 0 =
      embedRay hb fallback u := by
  simp [parameterElement]

/-- The tuple parameter a records the TRUE observed D₂
letters at their actual marked root, coordinate by coordinate. -/
theorem parameterElement_bullet_letter
    {b N q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) (a : Fin q → β)
    (i : BulletIndex (kind q)) :
    (parameterElement hb fallback u a).words i.1
        ((parameterElement hb fallback u a).bulletPoint i) =
      a (bulletCoordinate i) := by
  have hi : i.1 ≠ (0 : Fin (q + 1)) :=
    bullet_ne_zero i
  simp [parameterElement, hi, endWordValue]

/-- A word in the genuine LAST-root singleton variable span
is determined by its observed letter at that root.
The claim is independent of the other mixed coordinates. -/
theorem endK_span_word_eq
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : TreeWord b (N + 1) β)
    (hu : u ∈ (endKVariableWord hb N fallback).span) :
    u = endWordValue hb N fallback (u (endRoot hb N)) := by
  obtain ⟨τ, hτ⟩ := hu
  have heval := endVariableWord_eval (N := N) hb fallback τ
  have hword : u =
      endWordValue hb N fallback (τ (endVar hb N)) :=
    hτ.symm.trans heval
  have hroot : u (endRoot hb N) = τ (endVar hb N) := by
    have ht := congrFun hword (endRoot hb N)
    simpa [endWordValue] using ht
  calc
    u = endWordValue hb N fallback (τ (endVar hb N)) := hword
    _ = endWordValue hb N fallback (u (endRoot hb N)) := by
      rw [hroot]

/-- Every D₂ point in the actual mixed span is the fixed last
root of the ray, and all of its letters remain independent. -/
theorem bulletPoint_eq_endRoot
    {b N q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) (q + 1) β (kind q))
    (hx : x ∈ (mixedWord hb w fallback r hroot hfirst q).span)
    (i : BulletIndex (kind q)) :
    x.bulletPoint i = endRoot hb N := by
  have hi := bullet_ne_zero i
  have h := hx.2.2 i
  change x.bulletPoint i ∈
    (if i.1 = 0 then
      (rayKVariableWord hb w fallback r hroot hfirst).support
    else (endKVariableWord hb N fallback).support) at h
  simpa [hi, endKVariableWord, endVariableWord] using h

/-- A genuine point of the mixed span has an ordinary D₀
HJ evaluation and an independent q-tuple of D₂ letters.
No additional starred, smoothness or choice assumptions
are introduced. -/
theorem span_element_eq_parameterElement
    {b N q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) (q + 1) β (kind q))
    (hx : x ∈ (mixedWord hb w fallback r hroot hfirst q).span) :
    ∃ σ : Fin 1 → β, ∃ a : Fin q → β,
      x = parameterElement hb fallback (SpanAudit.eval w σ) a := by
  have hplain :
      x.words 0 ∈
        (rayKVariableWord hb w fallback r hroot hfirst).span :=
    hx.1 0
  obtain ⟨τ, hτ⟩ := hplain
  let σ : Fin 1 → β := fun _ => τ (rootVar hb r)
  let a : Fin q → β :=
    fun j => x.words (Fin.succ j) (endRoot hb N)
  have hw0 : x.words 0 =
      embedRay hb fallback (SpanAudit.eval w σ) := by
    calc
      x.words 0 =
          (rayKVariableWord hb w fallback r hroot hfirst).toVariableWord.eval τ :=
        hτ.symm
      _ = embedRay hb fallback
          (SpanAudit.eval w (fun _ => τ (rootVar hb r))) :=
        rayVariableWord_eval hb w fallback r hroot hfirst τ
      _ = embedRay hb fallback (SpanAudit.eval w σ) := rfl
  have hother : ∀ i : Fin (q + 1), i ≠ 0 →
      x.words i = endWordValue hb N fallback
        (a (bulletCoordinate
          ⟨i, by simp [kind, ‹i ≠ 0›]⟩)) := by
    intro i hi
    have hm : x.words i ∈
        (endKVariableWord hb N fallback).span := by
      have h := hx.1 i
      change x.words i ∈
        (if i = 0 then
          (rayKVariableWord hb w fallback r hroot hfirst).span
        else (endKVariableWord hb N fallback).span) at h
      simpa [hi] using h
    have heval := endK_span_word_eq hb fallback (x.words i) hm
    let bi : BulletIndex (kind q) := ⟨i, by simp [kind, hi]⟩
    have hidx : Fin.succ (bulletCoordinate bi) = i :=
      succ_bulletCoordinate bi
    have ha :
        a (bulletCoordinate bi) =
          x.words i (endRoot hb N) := by
      change x.words (Fin.succ (bulletCoordinate bi))
        (endRoot hb N) = _
      rw [hidx]
    exact heval.trans (by rw [ha])
  have hwords : x.words =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).words := by
    funext i
    by_cases hi : i = 0
    · subst i
      exact hw0.trans
        (parameterElement_plain hb fallback (SpanAudit.eval w σ) a).symm
    · change x.words i =
        (if h : i = 0 then embedRay hb fallback (SpanAudit.eval w σ)
        else endWordValue hb N fallback
          (a (bulletCoordinate ⟨i, by simp [kind, h]⟩)))
      simpa [hi] using hother i hi
  have hup : x.upPoint =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).upPoint := by
    funext i
    exact False.elim (noUp i)
  have hbullet : x.bulletPoint =
      (parameterElement hb fallback (SpanAudit.eval w σ) a).bulletPoint := by
    funext i
    exact bulletPoint_eq_endRoot hb w fallback r hroot hfirst x hx i
  refine ⟨σ, a, ?_⟩
  cases x with
  | mk words up bullet =>
    change words = _ at hwords
    change up = _ at hup
    change bullet = _ at hbullet
    cases hwords
    cases hup
    cases hbullet
    rfl

end DualTree.PlainBulletBlock
