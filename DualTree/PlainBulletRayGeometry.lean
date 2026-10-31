import DualTree.VectorOrderedSingletonPair
import DualTree.RayHalesJewett
import DualTree.MixedProduct

/-!
# Genuine two-root D₀/D₂ mixed-product geometry at intrinsic height one

A c-good D₀/D₂ word cannot in general identify the D₀ variable root
with the marked D₂ variable root: a colouring may read the D₀ letter
at that D₂ marker. The first positive mixed construction therefore
uses TWO different variable-root positions on a fixed ray.

Given a proper flat Hales–Jewett line of N slots with first variable
at r < N, place the D₀ word on levels 0,...,N-1; place the D₂
variable only at the new ray node at level N. The two singleton
support roots have lengths r < N, so the FULL vector 1-complete-skew
geometry is satisfied by the ordered-singleton lemma.

This file proves the actual tree-variable-word and mixed-product
well-formedness statements. It does not yet invoke any colouring
or claim a Ramsey witness; the next file uses uniform finite-parameter
Hales–Jewett to prove c-goodness of the generated mixed span.
-/

namespace DualTree.PlainBulletRay

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- The first coordinate is D₀, the second is D₂. -/
def kind : Fin 2 → CoordKind :=
  fun i => if i = 0 then CoordKind.plain else CoordKind.bullet

/-- The actual D₁ index type is empty. -/
theorem noUp (i : UpIndex kind) : False := by
  by_cases h : i.1 = (0 : Fin 2)
  · have hi := i.2
    simp [kind, h] at hi
  · have hi := i.2
    simp [kind, h] at hi

/-- There is only one D₂ index, the second coordinate. -/
theorem bulletIndex_one (i : BulletIndex kind) :
    i.1 = (1 : Fin 2) := by
  have hne : i.1 ≠ (0 : Fin 2) := by
    intro h
    have hi := i.2
    simp [kind, h] at hi
  apply Fin.ext
  have hlt : i.1.val < 2 := i.1.isLt
  have hpos : i.1.val ≠ 0 := by
    intro hz
    apply hne
    apply Fin.ext
    exact hz
  omega

/-- The additional last ray node of length N is still
inside the finite homogeneous tree of height N+1. -/
def endRoot {b : Nat} (hb : 0 < b) (N : Nat) :
    BoundedNode b (N + 1) :=
  ⟨zeroRay hb N, by
    simp [InHomTree, zeroRay]⟩

/-- The genuine singleton variable name at the D₂ marker. -/
def endVar {b : Nat} (hb : 0 < b) (N : Nat) :
    {t : BoundedNode b (N + 1) // t ∈ [endRoot hb N]} :=
  ⟨endRoot hb N, by simp⟩

/-- An actual D₂ tree variable word. Its ONLY variable
occurrence is at endRoot; all other positions carry the
old-alphabet fallback constant. This ensures D₂ word
evaluations depend solely on their observed root letter. -/
noncomputable def endVariableWord
    {b : Nat} {β : Type*}
    (hb : 0 < b) (N : Nat) (fallback : β) :
    DualTree.VariableWord b (N + 1) β := by
  classical
  exact {
    support := [endRoot hb N]
    support_nodup := by simp
    word := fun t =>
      if t = endRoot hb N then Sum.inr (endVar hb N)
      else Sum.inl fallback
    atRoot := by
      intro v
      have hv : v = endVar hb N := by
        apply Subtype.ext
        change v.1 = endRoot hb N
        simpa using v.2
      subst v
      simp [endVar]
    below := by
      intro v t hvar
      have ht : t = endRoot hb N := by
        by_contra hne
        simp [hne] at hvar
      have hv : v.1 = endRoot hb N := by
        simpa using v.2
      rw [ht, hv]
      exact isPrefix_refl _
  }

/-- A genuine 1-complete skew D₂ coordinate word, not a
fictitious marked point without a variable root. -/
noncomputable def endKVariableWord
    {b : Nat} {β : Type*}
    (hb : 0 < b) (N : Nat) (fallback : β) :
    KVariableWord b (N + 1) 1 β
      (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := endVariableWord hb N fallback
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1
      [zeroRay hb N] = true
    exact SkewTree.singleton_complete_oneB _ _

/-- The D₂ evaluation at a chosen letter a: fixed fallback
everywhere except the unique marked root. -/
noncomputable def endWordValue
    {b : Nat} {β : Type*}
    (hb : 0 < b) (N : Nat) (fallback a : β) :
    TreeWord b (N + 1) β :=
  fun t => if t = endRoot hb N then a else fallback

theorem endWordValue_at_root
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback a : β) :
    endWordValue hb N fallback a (endRoot hb N) = a := by
  simp [endWordValue]

/-- Exact evaluation of the D₂ variable word, including its
fixed symbols outside the root. The marked letter determines
the ENTIRE D₂ word inside this generated span. -/
theorem endVariableWord_eval
    {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (σ : (endVariableWord hb N fallback).Vars → β) :
    (endVariableWord hb N fallback).eval σ =
      endWordValue hb N fallback (σ (endVar hb N)) := by
  classical
  funext t
  by_cases ht : t = endRoot hb N
  · simp [DualTree.VariableWord.eval, SpanAudit.eval,
      SpanAudit.evalSymbol, endVariableWord,
      endWordValue, ht]
  · simp [DualTree.VariableWord.eval, SpanAudit.eval,
      SpanAudit.evalSymbol, endVariableWord,
      endWordValue, ht]

/-- The genuine two-coordinate vector support has one root
at ray level r in D₀ and a different root at level N in D₂.
The full vector-complete-skew condition follows from r < N. -/
noncomputable def twoRootVectorWord
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    VectorVariableWord b (N + 1) 2 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := fun i =>
    if i = 0 then
      rayKVariableWord hb w fallback r hroot hfirst
    else endKVariableWord hb N fallback
  vector_complete := by
    change VectorSkew.vectorCompleteB
      SkewTree.forwardAuxB 1
      (VectorSkew.orderedSingletonPair
        (zeroRay hb r.val) (zeroRay hb N)) = true
    apply VectorSkew.orderedSingletonPair_vectorComplete_one
    simpa only [zeroRay, List.length_replicate]
      using (Nat.le_of_lt r.isLt)

/-- An ACTUAL mixed-product variable word with D₀ and D₂
both nonempty and D₁ empty. Its vector satisfies the
genuine full 1-complete skew support geometry. -/
noncomputable def twoRootMixedWord
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    MixedProduct.VariableWord b (N + 1) 2 1 β
      (SkewTree.forwardAuxB (b := b)) kind where
  vector := twoRootVectorWord hb w fallback r hroot hfirst
  upLeaves := fun i => False.elim (noUp i)
  upLeaves_nodup := fun i => False.elim (noUp i)
  upLeaves_card := fun i => False.elim (noUp i)
  up_support_skew := fun i => False.elim (noUp i)

/-- The marked point of ANY genuine member of this mixed
span is exactly the fixed D₂ end root, independently
of how its two coordinate variables were evaluated. -/
theorem bulletPoint_eq_endRoot
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (x : Element b (N + 1) 2 β kind)
    (hx : x ∈ (twoRootMixedWord hb w fallback r hroot hfirst).span)
    (i : BulletIndex kind) :
    x.bulletPoint i = endRoot hb N := by
  have h := hx.2.2 i
  rw [bulletIndex_one i] at h
  change x.bulletPoint i ∈ [endRoot hb N] at h
  simpa using h

end DualTree.PlainBulletRay
