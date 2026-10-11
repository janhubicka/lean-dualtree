import DualTree.VectorOneD2Characterization
import DualTree.ForwardQCertifiedSemiComplete
import Mathlib.Data.Finset.Sort

/-!
# Canonical increasing enumeration of the actual selected D₂ bullet indices

The selected D₂ indices of the repaired Q constructor form the
finite linearly ordered subtype
  BulletIndex (kind c) = {i : Fin d // kind c i = bullet}.
There is no need to assume externally an order-preserving
enumeration of this subtype. The pinned Mathlib finite-order
equivalence Fintype.orderIsoFinOfCardEq constructs a canonical
order isomorphism
  Fin (card D₂) ≃o D₂.

Together with VectorOneD2Characterization, this proves that:
* the exact vector-1-complete test on the canonical ordered
  singleton family is equivalent to BulletLengthsOrdered c x;
* the earlier order-correct Certificate c x can always be
  reconstructed from BulletLengthsOrdered c x;
* the actual corrected Q tree is semi-complete skew if that
  canonical vector-1 test holds.

These are source-facing conditions on the actual corrected
D₂ subtype, not invented bullet indices. This closes the
finite ordering/certificate-existence interface. The
additional statement that membership in the *printed* W_*
domain implies this canonical vector-1 condition has NOT
yet been formalized. The Q word g_w, colouring and final
Ramsey induction remain open.
-/

namespace DualTree.ForwardQCanonicalD2

open ForwardSourceQTree
open ForwardQIndexedTRanks

/-- The canonical increasing enumeration of the exact actual
selected D₂ subtype of the corrected Q mixed-product kind. -/
noncomputable def orderedBulletIso
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Fin (Fintype.card (MixedProduct.BulletIndex (kind c))) ≃o
      MixedProduct.BulletIndex (kind c) := by
  classical
  exact Fintype.orderIsoFinOfCardEq _ rfl

/-- The actual D₂ enumeration covers every selected bullet
coordinate, including the empty-D₂ case. -/
theorem orderedBulletIso_surjective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Surjective (orderedBulletIso c) :=
  (orderedBulletIso c).surjective

/-- The canonical enumeration preserves the inherited
sorted complete-frontier order on D₂. -/
theorem orderedBulletIso_order_preserve
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Fin (Fintype.card (MixedProduct.BulletIndex (kind c))))
    (hij : i < j) :
    ((orderedBulletIso c) i).1 < ((orderedBulletIso c) j).1 := by
  change (orderedBulletIso c) i < (orderedBulletIso c) j
  exact (orderedBulletIso c).strictMono hij

/-- No reversed D₂ order can be hidden by the subtype
enumeration: increasing underlying bullet indices imply
increasing canonical enumeration indices. -/
theorem orderedBulletIso_order_reflect
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Fin (Fintype.card (MixedProduct.BulletIndex (kind c))))
    (hij : ((orderedBulletIso c) i).1 <
      ((orderedBulletIso c) j).1) :
    i < j := by
  have h : (orderedBulletIso c) i < (orderedBulletIso c) j := hij
  simpa using (orderedBulletIso c).symm.strictMono h

/-- On the canonical selected bullet enumeration the exact
Definition 20 vector-one-complete condition has only one
nontrivial numerical constraint, the point-length order. -/
theorem canonical_vector_one_iff_bullet_lengths_ordered
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin
        (Fintype.card (MixedProduct.BulletIndex (kind c))) =>
          [(x.bulletPoint ((orderedBulletIso c) i)).1]) = true ↔
      BulletLengthsOrdered c x := by
  classical
  have hcharacterization :=
    VectorOneD2Characterization.vector_one_complete_iff_lengths_mono
      SkewTree.forwardAuxB
      (fun i : Fin
        (Fintype.card (MixedProduct.BulletIndex (kind c))) =>
          (x.bulletPoint ((orderedBulletIso c) i)).1)
  constructor
  · intro hvector i j hij
    obtain ⟨a, ha⟩ := (orderedBulletIso c).surjective i
    obtain ⟨b, hb⟩ := (orderedBulletIso c).surjective j
    have hab : a < b :=
      orderedBulletIso_order_reflect c a b (by
        simpa [ha, hb] using hij)
    have hlen := hcharacterization.mp hvector a b hab
    simpa [ha, hb] using hlen
  · intro hordered
    apply hcharacterization.mpr
    intro a b hab
    exact hordered (orderedBulletIso c a)
      (orderedBulletIso c b)
      (orderedBulletIso_order_preserve c a b hab)

/-- The exact old certificate no longer needs a separately
supplied enumeration: canonical increasing enumeration of the
actual selected bullet subtype is always available. -/
noncomputable def canonicalCertificate
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x) :
    ForwardQStarredD2Certificate.Certificate c x :=
  VectorOneD2Characterization.certificate_of_sorted_enumeration
    c x (Fintype.card (MixedProduct.BulletIndex (kind c)))
    (orderedBulletIso c)
    (orderedBulletIso_surjective c)
    (orderedBulletIso_order_reflect c)
    (orderedBulletIso_order_preserve c)
    hordered

/-- Without any extra finite enumeration assumptions,
existence of the actual selected-D₂ certificate is equivalent
to the exact bullet length-order condition. -/
theorem certificate_exists_iff_bullet_lengths_ordered
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    Nonempty (ForwardQStarredD2Certificate.Certificate c x) ↔
      BulletLengthsOrdered c x := by
  constructor
  · rintro ⟨cert⟩
    exact ForwardQStarredD2Certificate.bullet_lengths_ordered_of_certificate
      c x cert
  · intro hordered
    exact ⟨canonicalCertificate c x hordered⟩

/-- The actual repaired Q support is semi-complete skew whenever
the canonically enumerated selected D₂ singleton family is
vector-1-complete. The remaining W_* source-membership bridge
is explicitly *not* part of this geometric theorem. -/
theorem Q_semiComplete_of_canonical_D2_vectorOne
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hvector :
      VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
        (fun i : Fin
          (Fintype.card (MixedProduct.BulletIndex (kind c))) =>
            [(x.bulletPoint ((orderedBulletIso c) i)).1]) = true) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true :=
  ForwardQCertifiedSemiComplete.Q_semiComplete_of_bullet_lengths
    hb c x
    ((canonical_vector_one_iff_bullet_lengths_ordered c x).mp hvector)

end DualTree.ForwardQCanonicalD2
