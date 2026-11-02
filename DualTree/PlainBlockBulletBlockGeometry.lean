import DualTree.PlainBulletBlockRamsey
import DualTree.ParameterVectorHalesJewett
import DualTree.VectorRayHalesJewett
import DualTree.VectorOrderedSingletons

/-!
# Ordered singleton geometry for p ordinary D₀ and q marked D₂ components

This is the geometric lift needed to combine the verified
finite-parameter VECTOR Hales–Jewett theorem with genuine mixed
variable words. At intrinsic complete-skew height one, give
every D₀ coordinate the same EARLY variable root, but use
independent assignments to that variable in EACH component.
Give all D₂ coordinates a separate LATER root, again with
independent assignments in each component.

The original source coordinate order is preserved: first p
ordinary coordinates, then q marked coordinates. The roots
have weakly monotone ambient lengths, which is exactly the
FULL vector 1-complete-skew geometry in this case.

No D₁/up-leaf points are fabricated, and no marked-colour
uniformity or Ramsey conclusion is asserted in this file.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.FlatVectorHalesJewett
open DualTree.PlainBulletRay

/-- Initial block of p ordinary coordinates, followed by q
independent D₂ coordinates. The index width is p+q. -/
def kind (p q : Nat) : Fin (p + q) → CoordKind :=
  fun i => if i.val < p then CoordKind.plain else CoordKind.bullet

/-- No D₁/up coordinates exist in this genuine mixed partition. -/
theorem noUp {p q : Nat} (i : UpIndex (kind p q)) : False := by
  by_cases hi : i.1.val < p
  · have h := i.2
    simp [kind, hi] at h
  · have h := i.2
    simp [kind, hi] at h

/-- A D₂ coordinate is necessarily in the last block. -/
theorem bullet_ge_plain {p q : Nat}
    (i : BulletIndex (kind p q)) : p ≤ i.1.val := by
  by_contra h
  have hp : i.1.val < p := by omega
  have hi := i.2
  simp [kind, hp] at hi

/-- Identify a genuine D₂ subtype coordinate with its
independent retained letter index in Fin q. -/
def bulletCoordinate {p q : Nat}
    (i : BulletIndex (kind p q)) : Fin q :=
  ⟨i.1.val - p, by
    have hp : p ≤ i.1.val := bullet_ge_plain i
    have hlt : i.1.val < p + q := i.1.isLt
    omega⟩

/-- Include a D₂ letter index j into the actual mixed
coordinate array, without introducing a fake bullet index. -/
def bulletIndex (p q : Nat) (j : Fin q) :
    BulletIndex (kind p q) :=
  ⟨⟨p + j.val, by omega⟩, by
    simp [kind]⟩

theorem bulletCoordinate_bulletIndex
    (p q : Nat) (j : Fin q) :
    bulletCoordinate (bulletIndex p q j) = j := by
  apply Fin.ext
  simp [bulletCoordinate, bulletIndex]

/-- The geometric node used by each coordinate support:
an early common root of length r for D₀, and the later
root of length N for every D₂ coordinate. -/
def supportRoot {b N : Nat}
    (hb : 0 < b) (r : Fin N) (p q : Nat)
    (i : Fin (p + q)) : Node b :=
  if i.val < p then zeroRay hb r.val else zeroRay hb N

/-- Full cross-coordinate length ordering, including
cases in which the two indices lie in different blocks. -/
theorem supportRoot_lengths_monotone
    {b N : Nat}
    (hb : 0 < b) (r : Fin N) (p q : Nat)
    (i j : Fin (p + q))
    (hij : i < j) :
    (supportRoot hb r p q i).length ≤
      (supportRoot hb r p q j).length := by
  have hlt : i.val < j.val := hij
  by_cases hi : i.val < p
  · by_cases hj : j.val < p
    · simp [supportRoot, hi, hj]
    · simpa [supportRoot, hi, hj, zeroRay] using
        (Nat.le_of_lt r.isLt)
  · have hj : ¬ j.val < p := by omega
    simp [supportRoot, hi, hj]

/-- An honest vector-complete-skew family of p independent
D₀ tree words and q independent D₂ singleton-root words.
The D₀ words have synchronized variable positions but
independent substitution functions. All D₂ roots are later. -/
noncomputable def vectorWord
    {b N p : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (q : Nat) :
    VectorVariableWord b (N + 1) (p + q) 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := fun i =>
    if hi : i.val < p then
      VectorRayHalesJewett.coordinateRayWord hb w fallback
        r hroot hfirst ⟨i.val, hi⟩
    else
      endKVariableWord hb N fallback
  vector_complete := by
    have hs :
        (fun i : Fin (p + q) =>
          (if hi : i.val < p then
            VectorRayHalesJewett.coordinateRayWord hb w fallback
              r hroot hfirst ⟨i.val, hi⟩
           else endKVariableWord hb N fallback).toVariableWord.supportNodes) =
        (fun i => [supportRoot hb r p q i]) := by
      funext i
      by_cases hi : i.val < p
      · simp [hi, supportRoot,
          VectorRayHalesJewett.coordinateRayWord,
          rayKVariableWord, rayVariableWord, rayPos,
          DualTree.VariableWord.supportNodes]
      · simp [hi, supportRoot,
          endKVariableWord, endVariableWord, endRoot,
          DualTree.VariableWord.supportNodes]
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin (p + q) =>
        (if hi : i.val < p then
          VectorRayHalesJewett.coordinateRayWord hb w fallback
            r hroot hfirst ⟨i.val, hi⟩
         else endKVariableWord hb N fallback).toVariableWord.supportNodes) = true
    rw [hs]
    exact VectorSkew.monotone_singletons_vectorComplete_one
      _ (supportRoot hb r p q)
      (supportRoot_lengths_monotone hb r p q)

/-- An ACTUAL source-facing mixed variable word, with all p
D₀ positions and q marked D₂ positions present.
All up/D₁ proof obligations are discharged by their
genuinely empty subtype, not with dummy leaves. -/
noncomputable def mixedWord
    {b N p : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (q : Nat) :
    MixedProduct.VariableWord b (N + 1) (p + q) 1 β
      (SkewTree.forwardAuxB (b := b)) (kind p q) where
  vector := vectorWord hb w fallback r hroot hfirst q
  upLeaves := fun i => False.elim (noUp i)
  upLeaves_nodup := fun i => False.elim (noUp i)
  upLeaves_card := fun i => False.elim (noUp i)
  up_support_skew := fun i => False.elim (noUp i)

end DualTree.PlainBlockBulletBlock
