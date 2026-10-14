import DualTree.ForwardInverseConeTails
import DualTree.ForwardQAmbientFibreSmoothObservable

/-!
# Safe outside-cone original f-fibres are smooth-observable

This module combines two previously independent, source-facing repairs
of Lemma 27's corrected Q construction.

(1) ForwardInverseConeTails proves that EVERY genuine T-support root
    t above a selected outside-cut frontier with a safe intrinsic
    rank difference is uniquely of the form P_i(z). It also proves
    that t outside its actual marked Q support cone implies z is
    outside its selected D2 local marked-point cone.

(2) ForwardQAmbientFibreSmoothObservable proves Definition 21's
    smoothness equality for the genuine enlarged-alphabet decoder
    on the ENTIRE ORIGINAL f-variable fibre of P_i(z), not just
    the projected root itself.

Together these imply: if t is safe and outside all Gamma2 marked
Q support cones, then the actual canonical local address z is
observable; every occurrence of the original ambient variable v_t
has the SAME Q letter for a pair of smooth-related enlarged-starred
inputs. No Hall matching or independent local cone variables appear.

This closes the safe-root piece of the general simplicity pullback.
The remaining cases are source-constant/old/cut fibres, no selected
frontier, and out-of-safe-domain fallback fibres. The abstract
Definition 24 A=B1+B2 to corrected literal R partition identification
and the final Ramsey refinement are still unproved.
-/

namespace DualTree.ForwardQSafeFibreSmoothness

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord
open ForwardQProjectedSmoothObservables

/-- A safe complete-support root t above frontier i is outside
every Gamma2 actual projected marked-point cone. Its UNIQUE
recovered tail z must therefore lie in the observable part
of its D0/Gamma1/Gamma2 coordinate for the selected partition.
This is a geometric *derived* observability statement, not
an additional assumption on the local input words. -/
theorem safeRoot_observable_of_gamma2_exterior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (x : ForwardQEnlargedConstantWords.EnlargedInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (i : ForwardQFullFrontierWord.Index c)
    (t : {u : Node b // u ∈ c.T})
    (hprefix :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hbudget :
      SkewTree.heightAt c.T t.1 -
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 <
        k - (m + 1))
    (hexterior :
      ∀ j : MixedProduct.BulletIndex (kind c),
        gamma1 j = false →
        ¬ IsPrefix
          (markedProjection c
            (ForwardQEnlargedConstantWords.eraseAux c fallback x) j).1
          t.1) :
    ObservableLocal c gamma1
      (ForwardQEnlargedConstantWords.eraseAux c fallback x)
      i
      (ForwardInverseConeTails.relativeTail c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut i)
        t hprefix hbudget) := by
  let z : BoundedNode b (k - (m + 1)) :=
    ForwardInverseConeTails.relativeTail c.T c.hcomplete c.hnon
      (ForwardOrderedProjections.frontierAt c.T c.cut i)
      t hprefix hbudget
  by_cases hi : kind c i = MixedProduct.CoordKind.bullet
  · let j : MixedProduct.BulletIndex (kind c) := ⟨i, hi⟩
    cases hg : gamma1 j with
    | true =>
        exact observable_gamma1 c gamma1
          (ForwardQEnlargedConstantWords.eraseAux c fallback x)
          j hg z
    | false =>
        have hnot :=
          ForwardInverseConeTails.local_outside_of_safe_target_outside
            c (ForwardQEnlargedConstantWords.eraseAux c fallback x)
            j t hprefix hbudget (hexterior j hg)
        exact observable_gamma2_outside c gamma1
          (ForwardQEnlargedConstantWords.eraseAux c fallback x)
          j z hnot
  · exact observable_nonbullet c gamma1
      (ForwardQEnlargedConstantWords.eraseAux c fallback x)
      i hi z

/-- The full original f-fibre of a safe ambient root t has
identical Q output symbols under smooth-related enlarged-starred
inputs, provided t is outside ALL Gamma2 projected marked cones.
The root's representation t=P_i(z) is PROVED from the corrected
complete support, not added as an external premise. -/
theorem fibreQ_eq_on_safe_gamma2_exterior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (i : ForwardQAmbientFibreSymbol.Index c)
    (t : {u : Node b // u ∈ c.core.T})
    (hprefix :
      IsPrefix
        (ForwardOrderedProjections.frontierAt
          c.core.T c.core.cut i).1 t.1)
    (hbudget :
      SkewTree.heightAt c.core.T t.1 -
        SkewTree.heightAt c.core.T
          (ForwardOrderedProjections.frontierAt
            c.core.T c.core.cut i).1 <
        k - (m + 1))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c t.1 t.2))
    (hexterior :
      ∀ j : MixedProduct.BulletIndex (kind c.core),
        gamma1 j = false →
        ¬ IsPrefix
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback x.1) j).1 t.1) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  let z : BoundedNode b (k - (m + 1)) :=
    ForwardInverseConeTails.relativeTail
      c.core.T c.core.hcomplete c.core.hnon
      (ForwardOrderedProjections.frontierAt c.core.T c.core.cut i)
      t hprefix hbudget
  have hrecover :
      ForwardQActualCoordinateWord.projectLocal c.core i z = t :=
    ForwardInverseConeTails.projectCommon_reaches_target
      c.core.T c.core.hcomplete c.core.hnon
      c.core.cut c.core.hcutT c.core.hm
      (ForwardOrderedProjections.frontierAt c.core.T c.core.cut i)
      t (ForwardOrderedProjections.frontierAt_spec
        c.core.T c.core.cut i) hprefix hbudget
  have hsProjected :
      c.ambient.word s =
        Sum.inr (ambientAtTRoot c
          (ForwardQActualCoordinateWord.projectLocal c.core i z).1
          (ForwardQActualCoordinateWord.projectLocal c.core i z).2) := by
    rw [hrecover]
    exact hs
  have hobs : ObservableLocal c.core gamma1
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1)
      i z :=
    safeRoot_observable_of_gamma2_exterior c.core fallback x.1
      gamma1 i t hprefix hbudget hexterior
  exact ForwardQAmbientFibreSmoothObservable.Q_word_eq_on_observable_full_fibre
    hb c fallback x y gamma1 hxy i z s hsProjected hobs

end DualTree.ForwardQSafeFibreSmoothness
