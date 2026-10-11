import DualTree.ForwardQStarredD2Certificate

/-!
# Characterizing the vector-one-complete condition on selected D₂ points

For a finite ordered family of singleton support nodes
  i ↦ [s_i],
Definition 20's vector-one-completeness test simplifies to exactly
the nondecreasing ambient lengths condition
  i < j -> |s_i| <= |s_j|.

Both directions are established from the executable VectorSkew
definitions; the components are automatically 1-complete skew,
and the successive-level condition is vacuous at height 1.

For the genuine sorted D₂ coordinates of the corrected Q map,
an order-preserving, order-reflecting surjection of Fin d₂ onto
the bullet-index subtype turns the length-order condition into
a concrete typed Certificate and vice versa.

This identifies the mathematical content of the vector-one test
without asserting that the printed W_* domain has already been
encoded or that every arbitrary mixed-product point is starred.
The construction of the order-correct enumeration and extraction
of the relevant predicate from the printed W_* remain explicit tasks.
-/

namespace DualTree.VectorOneD2Characterization

open DualTree.ForwardSourceQTree
open DualTree.ForwardQIndexedTRanks

/-- On a singleton support the rank-zero list is precisely its
single node, without any skew or root condition. -/
theorem singleton_level_zero {b : Nat} (s : Node b) :
    VectorSkew.levelNodes [s] 0 = [s] := by
  simp [VectorSkew.levelNodes, SkewTree.heightAt, SkewTree.preds,
    SkewTree.strictPrefixB]

/-- Pairwise nondecreasing lengths make singleton vector supports
satisfy the exact Definition 20 same-level order predicate at
intrinsic height one. -/
theorem same_level_one_of_lengths_mono
    {b d : Nat} (point : Fin d → Node b)
    (hmono : ∀ (i j : Fin d), i < j →
      (point i).length ≤ (point j).length) :
    VectorSkew.sameLevelOrderedB
      (fun i : Fin d => [point i]) 1 = true := by
  unfold VectorSkew.sameLevelOrderedB
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro j _
  split_ifs with hij
  · simp [singleton_level_zero, hmono i j hij]
  · rfl

/-- The converse to the already verified
VectorOneMarkedLengths.lengths_mono_of_vectorOneComplete:
no extra cross-coordinate conditions remain for singleton
supports of intrinsic height one. -/
theorem vector_one_complete_of_lengths_mono
    {b d : Nat}
    (aux : Node b → Node b → Bool)
    (point : Fin d → Node b)
    (hmono : ∀ (i j : Fin d), i < j →
      (point i).length ≤ (point j).length) :
    VectorSkew.vectorCompleteB aux 1
      (fun i : Fin d => [point i]) = true := by
  have hcomponents :
      (SkewTree.allFin d).all
        (fun i => SkewTree.completeB aux 1 [point i]) = true := by
    apply List.all_eq_true.mpr
    intro i _
    exact SkewTree.singleton_complete_oneB aux (point i)
  have hsames := same_level_one_of_lengths_mono point hmono
  simp [VectorSkew.vectorCompleteB, VectorSkew.successiveLevelsSeparatedB,
    hcomponents, hsames]

/-- Exact finite singleton-vector formulation of Definition 20's
height-one cross-coordinate condition for every branching number,
dimension, and auxiliary node order. -/
theorem vector_one_complete_iff_lengths_mono
    {b d : Nat}
    (aux : Node b → Node b → Bool)
    (point : Fin d → Node b) :
    VectorSkew.vectorCompleteB aux 1
      (fun i : Fin d => [point i]) = true ↔
    ∀ (i j : Fin d), i < j →
      (point i).length ≤ (point j).length := by
  constructor
  · intro h i j hij
    exact VectorOneMarkedLengths.lengths_mono_of_vectorOneComplete
      aux point h i j hij
  · exact vector_one_complete_of_lengths_mono aux point

/-- Given a genuine sorted enumeration of all and only selected
D₂ indices, the monotone-length hypothesis reconstructs the
source-facing vector-one-complete certificate itself.
No assumption about unused D₀ coordinates is made. -/
noncomputable def certificate_of_sorted_enumeration
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (d2 : Nat)
    (enumerate : Fin d2 → MixedProduct.BulletIndex (kind c))
    (onto : Function.Surjective enumerate)
    (orderReflect : ∀ (i j : Fin d2),
      (enumerate i).1 < (enumerate j).1 → i < j)
    (orderPreserve : ∀ (i j : Fin d2),
      i < j → (enumerate i).1 < (enumerate j).1)
    (hordered : BulletLengthsOrdered c x) :
    ForwardQStarredD2Certificate.Certificate c x := {
  d2 := d2
  enumerate := enumerate
  onto := onto
  orderReflect := orderReflect
  vectorComplete := by
    apply vector_one_complete_of_lengths_mono
      SkewTree.forwardAuxB
      (fun i : Fin d2 =>
        (x.bulletPoint (enumerate i)).1)
    intro i j hij
    exact hordered (enumerate i) (enumerate j)
      (orderPreserve i j hij)
}

/-- Relative to one fixed order-correct exhaustive enumeration
of the actual D₂ subtype, the existence of a genuine
vector-one-complete certificate is *equivalent* to the
pairwise marked-length condition. The construction of a
canonical enumeration from the concrete marker map is
kept as a separate finite-order theorem obligation. -/
theorem exists_certificate_iff_bullet_lengths_of_sorted_enumeration
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (d2 : Nat)
    (enumerate : Fin d2 → MixedProduct.BulletIndex (kind c))
    (onto : Function.Surjective enumerate)
    (orderReflect : ∀ (i j : Fin d2),
      (enumerate i).1 < (enumerate j).1 → i < j)
    (orderPreserve : ∀ (i j : Fin d2),
      i < j → (enumerate i).1 < (enumerate j).1) :
    Nonempty (ForwardQStarredD2Certificate.Certificate c x) ↔
      BulletLengthsOrdered c x := by
  constructor
  · rintro ⟨cert⟩
    exact ForwardQStarredD2Certificate.bullet_lengths_ordered_of_certificate
      c x cert
  · intro hordered
    exact ⟨certificate_of_sorted_enumeration
      c x d2 enumerate onto orderReflect orderPreserve hordered⟩

end DualTree.VectorOneD2Characterization
