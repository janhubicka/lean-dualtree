import DualTree.PlainBulletRayGeometry
import DualTree.VectorOrderedSingletons

/-!
# One ordinary D₀ coordinate followed by arbitrarily many D₂ markers

For q retained D₂ marker-letter coordinates, give the D₀ word an
EARLIER singleton variable root on the all-zero ray and give each D₂
coordinate its own independent word variable at the SAME LATER ray
node. Repeating the geometric node across the D₂ components is
permitted: variables are assigned independently in each COMPONENT.
The source-facing vector-complete-skew condition requires weak
ambient-length ordering, which is verified by the general ordered
singleton lemma, not assumed.

The first coordinate is ordinary, the q later coordinates are marked,
and no D₁ up-leaf set is fabricated. This is tree-geometry
infrastructure for a q-parameter c-good mixed Ramsey theorem, not
yet a colouring or existence proof.
-/

namespace DualTree.PlainBulletBlock

open DualTree.MixedProduct
open DualTree.RayHalesJewett
open DualTree.PlainBulletRay

/-- An initial ordinary D₀ coordinate followed by q D₂ coordinates. -/
def kind (q : Nat) : Fin (q + 1) → CoordKind :=
  fun i => if i = 0 then CoordKind.plain else CoordKind.bullet

/-- There are no D₁ up-leaf coordinates in this mixed partition. -/
theorem noUp {q : Nat} (i : UpIndex (kind q)) : False := by
  by_cases hi : i.1 = (0 : Fin (q + 1))
  · have h := i.2
    simp [kind, hi] at h
  · have h := i.2
    simp [kind, hi] at h

/-- Every D₂ index differs from the initial D₀ index. -/
theorem bullet_ne_zero {q : Nat}
    (i : BulletIndex (kind q)) :
    i.1 ≠ (0 : Fin (q + 1)) := by
  intro hi
  have h := i.2
  simp [kind, hi] at h

/-- Reindex the genuine D₂ marker coordinates by Fin q,
without identifying their independent observed letters. -/
def bulletCoordinate {q : Nat}
    (i : BulletIndex (kind q)) : Fin q :=
  ⟨i.1.val - 1, by
    have hne : i.1.val ≠ 0 := by
      intro hzero
      apply bullet_ne_zero i
      apply Fin.ext
      exact hzero
    have hlt : i.1.val < q + 1 := i.1.isLt
    omega⟩

/-- Each D₂ marker j occurs in the actual mixed coordinate
Fin (q+1) at the successor index; no bullets exist when q=0. -/
def bulletIndex (q : Nat) (j : Fin q) :
    BulletIndex (kind q) :=
  ⟨Fin.succ j, by simp [kind]⟩

/-- The reindexing of actual D₂ markers is a left inverse
to their embedding as successor coordinates. -/
theorem bulletCoordinate_bulletIndex
    (q : Nat) (j : Fin q) :
    bulletCoordinate (bulletIndex q j) = j := by
  apply Fin.ext
  simp [bulletCoordinate, bulletIndex, Fin.succ]

/-- First coordinate support is the Hales–Jewett root at
ray level r, while ALL later D₂ supports are at level N. -/
def supportRoot {b N : Nat}
    (hb : 0 < b) (r : Fin N) (q : Nat)
    (i : Fin (q + 1)) : Node b :=
  if i = 0 then zeroRay hb r.val else zeroRay hb N

/-- These root lengths are weakly increasing in the
source's coordinate order, and are strictly separated
between the D₀ coordinate and every D₂ coordinate. -/
theorem supportRoot_lengths_monotone
    {b N : Nat}
    (hb : 0 < b) (r : Fin N) (q : Nat)
    (i j : Fin (q + 1))
    (hij : i < j) :
    (supportRoot hb r q i).length ≤
      (supportRoot hb r q j).length := by
  have hlt : i.val < j.val := hij
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by
      intro hzero
      have hz : j.val = 0 := congrArg Fin.val hzero
      omega
    simp [supportRoot, hi, hj, zeroRay]
  · have hj : j ≠ 0 := by
      intro hzero
      have hz : j.val = 0 := congrArg Fin.val hzero
      omega
    simp [supportRoot, hi, hj]

/-- An ACTUAL vector 1-complete-skew family: one genuine
root-aligned Hales–Jewett D₀ tree variable word, followed
by q independent D₂ tree words with the same later
geometric root but independent substitution maps. -/
noncomputable def vectorWord
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (q : Nat) :
    VectorVariableWord b (N + 1) (q + 1) 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := fun i =>
    if i = 0 then
      rayKVariableWord hb w fallback r hroot hfirst
    else endKVariableWord hb N fallback
  vector_complete := by
    have hs :
        (fun i : Fin (q + 1) =>
          (if i = 0 then
            rayKVariableWord hb w fallback r hroot hfirst
           else endKVariableWord hb N fallback).toVariableWord.supportNodes) =
        (fun i => [supportRoot hb r q i]) := by
      funext i
      by_cases hi : i = 0
      · simp [hi, supportRoot,
          rayKVariableWord, rayVariableWord, rayPos,
          DualTree.VariableWord.supportNodes]
      · simp [hi, supportRoot,
          endKVariableWord, endVariableWord, endRoot,
          DualTree.VariableWord.supportNodes]
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin (q + 1) =>
        (if i = 0 then
          rayKVariableWord hb w fallback r hroot hfirst
         else endKVariableWord hb N fallback).toVariableWord.supportNodes) = true
    rw [hs]
    exact VectorSkew.monotone_singletons_vectorComplete_one
      _ (supportRoot hb r q)
      (supportRoot_lengths_monotone hb r q)

/-- The corresponding ACTUAL mixed variable word with q retained
D₂ coordinates and no D₁, rather than an abstract product word.
Every D₂ coordinate has its own substitution even though its
marked root occupies the same last ray node. -/
noncomputable def mixedWord
    {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (q : Nat) :
    MixedProduct.VariableWord b (N + 1) (q + 1) 1 β
      (SkewTree.forwardAuxB (b := b)) (kind q) where
  vector := vectorWord hb w fallback r hroot hfirst q
  upLeaves := fun i => False.elim (noUp i)
  upLeaves_nodup := fun i => False.elim (noUp i)
  upLeaves_card := fun i => False.elim (noUp i)
  up_support_skew := fun i => False.elim (noUp i)

end DualTree.PlainBulletBlock
