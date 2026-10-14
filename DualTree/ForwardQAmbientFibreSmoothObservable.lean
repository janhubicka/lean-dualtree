import DualTree.ForwardQSimpleLetterSmooth
import DualTree.ForwardQProjectedSmoothObservables

/-!
# Definition 21 observable local letters on genuine ambient f fibres

The corrected Q word now uses the original complete-support ambient variable
word f and reads each local enlarged letter at the ROOT of a whole f-variable
fibre.  Prior observable-Q lemmas compared the different, simpler Q
coordinate-word construction only at projected P_i(z) positions.

We transport the observable mask of a general Gamma1/Gamma2 split to the
actual enlarged-alphabet mixed-product coordinates (original letters PLUS
the m+1 auxiliary letters).  For each observable local address z, the
entire fibre f^{-1}(v_{P_i(z)}) carries the SAME Q symbol under any two
smooth-related starred mixed inputs.  Gamma1 fixes all coordinate words;
Gamma2 fixes outside-marked-cone letters and the marked point itself.

This is strictly stronger than equality solely at P_i(z), since an
original f-variable may occur at arbitrarily many ambient positions.
It is strictly weaker than the full Lemma 27 simplicity transport:
we do not yet prove that every original f-variable root relevant
outside the B2 Q-cones is represented by a safe observable P_i(z),
nor identify Definition 24's abstract A/B1/B2 with the corrected
literal marker set R.  The corrected global order and syntactic
source-refinement premises remain explicit in FibreFrame.
-/

namespace DualTree.ForwardQAmbientFibreSmoothObservable

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQAmbientFibreSymbol
open ForwardQProjectedSmoothObservables

/-- Definition 21 smoothness fixes the ACTUAL enlarged input
letter at each observable local tail, including auxiliary symbols.
The observable predicate uses erased words only to recover the
identical selected bullet-point geometry, never for letter values. -/
theorem enlarged_letter_eq_of_smooth_observable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y)
    (i : ForwardQFullFrontierWord.Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hobs : ObservableLocal c gamma1
      (ForwardQEnlargedConstantWords.eraseAux c fallback x) i z) :
    x.words i z = y.words i z := by
  rcases hobs with hplain | ⟨j, rfl, hcase⟩
  · exact congrFun (hxy.1 i hplain) z
  · cases hg : gamma1 j with
    | true =>
        have hword : x.words j.1 = y.words j.1 := by
          simpa [hg] using hxy.2.2 j
        exact congrFun hword z
    | false =>
        rcases hcase with htrue | hout
        · simp [hg] at htrue
        · have hpair :
              x.bulletPoint j = y.bulletPoint j ∧
                ∀ t : BoundedNode b (k - (m + 1)),
                  ¬ IsPrefix (x.bulletPoint j).1 t.1 →
                    x.words j.1 t = y.words j.1 t := by
            simpa [hg] using hxy.2.2 j
          exact hpair.2 z hout

/-- The genuine fibrewise Q output words agree at EVERY position
of an original f-variable fibre rooted at P_i(z), provided z
is observable under the arbitrary Gamma1/Gamma2 partition.
This includes occurrences that are not T-support vertices and
have no safe inverse support address of their own. Such occurrences
still lie above the original f-root and therefore INSIDE its
containing frontier cone, as guaranteed by VariableWord.below. -/
theorem Q_word_eq_on_observable_full_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (i : ForwardQAmbientFibreSymbol.Index c)
    (z : BoundedNode b (k - (m + 1)))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).2))
    (hobs : ObservableLocal c.core gamma1
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1) i z) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  have hletter :=
    enlarged_letter_eq_of_smooth_observable
      c.core gamma1 fallback x.1 y.1 hxy i z hobs
  change fibreQSymbol c fallback x.1 s =
    fibreQSymbol c fallback y.1 s
  rw [ForwardQAmbientFibreSymbol.fibreQ_projected_full_fibre
        c fallback x.1 i z s hs,
      ForwardQAmbientFibreSymbol.fibreQ_projected_full_fibre
        c fallback y.1 i z s hs]
  exact congrArg
    (fun letter : Sum α (Fin (m + 1)) =>
      match letter with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j) hletter

/-- Every genuine D0/plain coordinate is entirely observable:
its Q symbol agrees on the complete original f-fibre
through EVERY projected local address. -/
theorem Q_word_eq_on_plain_full_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (i : ForwardQAmbientFibreSymbol.Index c)
    (hi : kind c.core i ≠ MixedProduct.CoordKind.bullet)
    (z : BoundedNode b (k - (m + 1)))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).2)) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  exact Q_word_eq_on_observable_full_fibre hb c fallback
    x y gamma1 hxy i z s hs
    (observable_nonbullet c.core gamma1
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1)
      i hi z)

/-- Every Gamma1 selected D2 coordinate preserves full
local words, even when its selected marked point moves. -/
theorem Q_word_eq_on_gamma1_full_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (j : MixedProduct.BulletIndex (kind c.core))
    (hj : gamma1 j = true)
    (z : BoundedNode b (k - (m + 1)))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core j.1 z).1
        (ForwardQActualCoordinateWord.projectLocal c.core j.1 z).2)) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  exact Q_word_eq_on_observable_full_fibre hb c fallback
    x y gamma1 hxy j.1 z s hs
    (observable_gamma1 c.core gamma1
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1)
      j hj z)

/-- At Gamma2 the Q words agree throughout a full original
f-variable fibre when its intrinsic local tail lies OUTSIDE
the selected marked local successor cone. No unsupported
agreement is asserted for tails inside the cone. -/
theorem Q_word_eq_on_gamma2_outside_full_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (j : MixedProduct.BulletIndex (kind c.core))
    (z : BoundedNode b (k - (m + 1)))
    (hout : ¬ IsPrefix (x.1.bulletPoint j).1 z.1)
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core j.1 z).1
        (ForwardQActualCoordinateWord.projectLocal c.core j.1 z).2)) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  exact Q_word_eq_on_observable_full_fibre hb c fallback
    x y gamma1 hxy j.1 z s hs
    (observable_gamma2_outside c.core gamma1
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1)
      j z hout)

/-- Smoothness also fixes the genuine projected Q marked
support node at every Gamma2 coordinate.  The Gamma1
points are intentionally NOT asserted equal. -/
theorem gamma2_Q_markedProjection_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (j : MixedProduct.BulletIndex (kind c.core))
    (hj : gamma1 j = false) :
    markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1) j =
      markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux c.core fallback y.1) j := by
  have hpoint : x.1.bulletPoint j = y.1.bulletPoint j := by
    have hp :
        x.1.bulletPoint j = y.1.bulletPoint j ∧
          (∀ t : BoundedNode b (k - (m + 1)),
            ¬ IsPrefix (x.1.bulletPoint j).1 t.1 →
              x.1.words j.1 t = y.1.words j.1 t) := by
      simpa [hj] using hxy.2.2 j
    exact hp.1
  simp [markedProjection, ForwardQEnlargedConstantWords.eraseAux, hpoint]

end DualTree.ForwardQAmbientFibreSmoothObservable
