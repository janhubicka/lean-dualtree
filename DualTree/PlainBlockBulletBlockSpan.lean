import DualTree.PlainBlockBulletBlockParameters
import DualTree.PlainBulletBlockSpan

/-!
# Source-faithful mixed span representation: p D₀ and q D₂ coordinates

A genuine mixed word with synchronized one-variable D₀ coordinate
words and q independent later marked D₂ variables has the exact
pointwise representation required by finite-parameter vector
Hales–Jewett: one independent ordinary assignment per D₀
component, and one independently chosen observed letter per D₂
component. We prove the forward containment using the ACTUAL
MixedProduct.VariableWord.span (not a postulated representation).

The reverse inclusion and full record c-good theorem are
subsequent obligations. D₁ leaf data and higher intrinsic
height remain outside this base case.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay
open DualTree.FlatVectorHalesJewett

/-- Every true mixed span point has a tuple of p independent
ordinary Hales–Jewett variable assignments and q independent
D₂ marked letters. The D₂ words are determined exactly by
the observed root letters, and all D₂ points are the fixed
later root. -/
theorem span_element_eq_parameterElement
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) (p + q) β (kind p q))
    (hx : x ∈ (mixedWord hb w fallback r hroot hfirst q).span) :
    ∃ σ : Fin p → Fin 1 → β, ∃ a : Fin q → β,
      x = parameterElement hb fallback
        (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a := by
  classical
  have hplain (j : Fin p) :
      x.words (plainIndex p q j) ∈
        (DualTree.VectorRayHalesJewett.coordinateRayWord
          hb w fallback r hroot hfirst j).span := by
    have h := hx.1 (plainIndex p q j)
    simpa [mixedWord, vectorWord, plainIndex, j.isLt]
      using h
  have hchoice (j : Fin p) :
      ∃ τ :
        (DualTree.VectorRayHalesJewett.coordinateRayWord
          hb w fallback r hroot hfirst j).Vars → β,
        (DualTree.VectorRayHalesJewett.coordinateRayWord
          hb w fallback r hroot hfirst j).toVariableWord.eval τ =
            x.words (plainIndex p q j) :=
    hplain j
  let τ (j : Fin p) :=
    Classical.choose (hchoice j)
  have hτ (j : Fin p) :
      (DualTree.VectorRayHalesJewett.coordinateRayWord
        hb w fallback r hroot hfirst j).toVariableWord.eval (τ j) =
          x.words (plainIndex p q j) :=
    Classical.choose_spec (hchoice j)
  let σ : Fin p → Fin 1 → β :=
    fun j _ => (τ j) (rootVar hb r)
  let a : Fin q → β :=
    fun j => x.words (bulletIndex p q j).1 (endRoot hb N)
  have hw0 (j : Fin p) :
      x.words (plainIndex p q j) =
        embedRay hb fallback
          (SpanAudit.eval (coordinateWord w j) (σ j)) := by
    calc
      x.words (plainIndex p q j) =
        (DualTree.VectorRayHalesJewett.coordinateRayWord
          hb w fallback r hroot hfirst j).toVariableWord.eval (τ j) :=
        (hτ j).symm
      _ = embedRay hb fallback
          (SpanAudit.eval (coordinateWord w j)
            (fun _ => (τ j) (rootVar hb r))) :=
        DualTree.VectorRayHalesJewett.coordinateRayWord_eval
          hb w fallback r hroot hfirst j (τ j)
      _ = embedRay hb fallback
          (SpanAudit.eval (coordinateWord w j) (σ j)) := rfl
  have hother (i : BulletIndex (kind p q)) :
      x.words i.1 =
        endWordValue hb N fallback (a (bulletCoordinate i)) := by
    have hi : ¬i.1.val < p :=
      not_lt.mpr (bullet_ge_plain i)
    have hm :
        x.words i.1 ∈ (endKVariableWord hb N fallback).span := by
      have h := hx.1 i.1
      simpa [mixedWord, vectorWord, hi] using h
    have heval :=
      PlainBulletBlock.endK_span_word_eq
        hb fallback (x.words i.1) hm
    have hidx : (bulletIndex p q (bulletCoordinate i)).1 = i.1 :=
      bulletIndex_bulletCoordinate i
    have ha :
        a (bulletCoordinate i) =
          x.words i.1 (endRoot hb N) := by
      change x.words (bulletIndex p q (bulletCoordinate i)).1
        (endRoot hb N) = _
      rw [hidx]
    exact heval.trans (by rw [ha])
  have hwords :
      x.words =
        (parameterElement hb fallback
          (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a).words := by
    funext i
    by_cases hi : i.val < p
    · let j : Fin p := plainCoordinate i hi
      have heq : plainIndex p q j = i :=
        plainIndex_plainCoordinate i hi
      have hw := hw0 j
      rw [heq] at hw
      simpa [parameterElement, hi, j, plainCoordinate] using hw
    · let bi : BulletIndex (kind p q) :=
        ⟨i, by simp [kind, hi]⟩
      have h := hother bi
      simpa [parameterElement, hi, bi] using h
  have hup : x.upPoint =
      (parameterElement hb fallback
        (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a).upPoint := by
    funext i
    exact False.elim (noUp i)
  have hbullet : x.bulletPoint =
      (parameterElement hb fallback
        (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a).bulletPoint := by
    funext i
    exact bulletPoint_eq_endRoot hb w fallback r hroot hfirst x hx i
  refine ⟨σ, a, ?_⟩
  exact PlainBulletBlock.element_eq_of_fields x
    (parameterElement hb fallback
      (fun j => SpanAudit.eval (coordinateWord w j) (σ j)) a)
    hwords hup hbullet

end DualTree.PlainBlockBulletBlock
