import DualTree.ForwardQIndexedTRanks
import DualTree.VectorOneMarkedLengths

/-!
# A typed bridge from starred D₂ vector completeness to Q length order

The corrected Q source construction has actual selected D₂ bullet
indices of type BulletIndex (kind c), a subtype of the *sorted*
Fin d frontier positions. Definition 20's vector-one-complete
condition is naturally expressed on a consecutive finite list
of precisely these D₂ coordinates, not on all D₀ and D₂
coordinates mixed together.

The certificate below keeps this distinction explicit:
* enumerate the actual D₂ coordinates by Fin d2, surjectively;
* require that their order reflects the sorted ambient Fin d order;
* require that the singleton supports of the selected local marked
  points form a genuine vector 1-complete skew family.

The existing kernel-checked VectorOneMarkedLengths theorem then
implies BulletLengthsOrdered for *every selected D₂ pair*, which
was the exact hypothesis of the new ambient T rank/length
monotonicity lemmas.

Constructing this certificate from every printed W_* object,
including any treatment of D₁ or the paper's remaining domain
restrictions, is a separate source-facing obligation. No such
construction or equivalence is assumed here.
-/

namespace DualTree.ForwardQStarredD2Certificate

open ForwardSourceQTree
open ForwardQIndexedTRanks

/-- A concrete, order-correct singleton vector realization of
the actual selected bullet point coordinates. -/
structure Certificate
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c) where
  d2 : Nat
  enumerate : Fin d2 → MixedProduct.BulletIndex (kind c)
  onto : Function.Surjective enumerate
  orderReflect :
    ∀ i j : Fin d2,
      (enumerate i).1 < (enumerate j).1 → i < j
  vectorComplete :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin d2 => [(x.bulletPoint (enumerate i)).1]) = true

/-- A genuinely vector-one-complete ordered enumeration of the
selected D₂ points enforces the pairwise local marked-point
length monotonicity required by the repaired Q projection. -/
theorem bullet_lengths_ordered_of_certificate
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c)
    (cert : Certificate c x) :
    BulletLengthsOrdered c x := by
  intro i j hij
  obtain ⟨a, ha⟩ := cert.onto i
  obtain ⟨b, hb⟩ := cert.onto j
  have hab : a < b :=
    cert.orderReflect a b (by simpa [ha, hb] using hij)
  have hl :=
    VectorOneMarkedLengths.lengths_mono_of_vectorOneComplete
      SkewTree.forwardAuxB
      (fun z : Fin cert.d2 =>
        (x.bulletPoint (cert.enumerate z)).1)
      cert.vectorComplete a b hab
  simpa [ha, hb] using hl

/-- The certificate transfers actual D₂ vector completeness
to monotonicity of enclosing T support ranks of projections. -/
theorem marked_T_rank_mono_of_certificate
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c)
    (cert : Certificate c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    SkewTree.heightAt c.T (markedProjection c x i).1 ≤
      SkewTree.heightAt c.T (markedProjection c x j).1 :=
  ForwardQIndexedTRanks.marked_T_rank_mono_of_bullet_order
    c x (bullet_lengths_ordered_of_certificate c x cert)
    i j hij

/-- The same source-domain certificate transfers to monotone
ambient word lengths of the actual selected Q projected leaves. -/
theorem marked_length_mono_of_certificate
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (x : Input c)
    (cert : Certificate c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1) :
    (markedProjection c x i).1.length ≤
      (markedProjection c x j).1.length :=
  ForwardQIndexedTRanks.marked_length_mono_of_bullet_order
    c x (bullet_lengths_ordered_of_certificate c x cert)
    i j hij

end DualTree.ForwardQStarredD2Certificate
