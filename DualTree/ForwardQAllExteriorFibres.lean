import DualTree.ForwardQFibreDefaults

/-!
# Global Gamma2-exterior equality for the actual ambient-fibrewise Q

This module combines all completed cases of the corrected Q decoder.
At an arbitrary ambient position s, the ORIGINAL ambient word f(s)
is either a constant or an original f-variable. Early/cut variables
are fixed by g'. For a late root, inspect the genuine selected
forward-complete frontier:
  * none: the original fallback letter;
  * some i and a local inverse support tail beyond the safe domain:
    the same fallback letter;
  * some i and a safe local tail: its T-support root is uniquely
    P_i(z), and the previously verified safe-exterior theorem applies.

The ONLY premise in the last case is that the original f-variable
ROOT itself is outside all selected Gamma2 Q marked-point cones.
Consequently two smooth-related enlarged mixed inputs yield equal
decoded output letters at EVERY original ambient position s whose
f-root is Gamma2-exterior. No extra assumption on the ambient
position's geometric cone is used: Q is constant on f-fibres.

The result is independent of Definition 24's abstract A/B1/B2
canonical-signature transport, which must still be checked to
deduce the specific simple-colouring pullback. It also does not
prove the final mixed-product variable-word Ramsey refinement.
-/

namespace DualTree.ForwardQAllExteriorFibres

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord

/-- The genuine inverse suffix length at ANY T-support node equals
the intrinsic support-rank difference from the selected frontier.
No local safe-height hypothesis is needed for the equality itself. -/
theorem tailOfTNode_length_eq_rank_diff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c)
    (t : {u : Node b // u ∈ c.T}) :
    (ForwardQActualCoordinateWord.tailOfTNode c i t).length =
      SkewTree.heightAt c.T t.1 -
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  simp only [ForwardQActualCoordinateWord.tailOfTNode, List.length_drop]
  rw [ForwardCompleteBijection.inverse_length
      c.T c.hcomplete c.hnon t,
      ForwardCompleteBijection.inverse_length
      c.T c.hcomplete c.hnon
      (ForwardOrderedProjections.frontierAt c.T c.cut i)]

/-- The precise outside-Gamma2 hypothesis is on the actual original
f-variable ROOT, not on an arbitrary ambient occurrence. Constants
have no original f-variable root and satisfy the predicate vacuously. -/
def RootGamma2Exterior
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (s : BoundedNode b n) : Prop :=
  ∀ v : c.ambient.Vars,
    c.ambient.word s = Sum.inr v →
      ∀ j : MixedProduct.BulletIndex (kind c.core),
        gamma1 j = false →
          ¬ IsPrefix
            (markedProjection c.core
              (ForwardQEnlargedConstantWords.eraseAux
                c.core fallback x) j).1 v.1.1

/-- Source-facing TOTAL exterior-word comparison for the actual
corrected Q. Exhausts original constants, early variable fibres,
no-frontier late fibres, unsafe local suffixes, and SAFE descendants
of the genuine selected frontier. The latter are handled by exact
support-cone recovery, not by pretending that every target is
defined by a chosen local coordinate in advance. -/
theorem starred_Q_word_eq_of_root_gamma2_exterior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (s : BoundedNode b n)
    (hexterior : RootGamma2Exterior c fallback x.1 gamma1 s) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  rw [fibreQStarredWord_symbol hb c fallback x s,
      fibreQStarredWord_symbol hb c fallback y s]
  cases hf : c.ambient.word s with
  | inl a =>
      exact ForwardQFibreDefaults.equal_at_ambient_constant
        c fallback x.1 y.1 s a hf
  | inr v =>
      by_cases hbefore : ForwardAux v.1.1 c.core.cut
      · exact ForwardQFibreDefaults.equal_on_early_fibre
          c fallback x.1 y.1 s v hf hbefore
      · cases hsel :
          ForwardQFullFrontierWord.selectedFrontier
            c.core v.1 with
        | none =>
            exact ForwardQFibreDefaults.equal_on_no_frontier_fibre
              c fallback x.1 y.1 s v hf hbefore hsel
        | some i =>
            have ht : v.1.1 ∈ c.core.T :=
              (c.ambient_support_T v.1).1 v.2
            let t : {u : Node b // u ∈ c.core.T} :=
              ⟨v.1.1, ht⟩
            have hprefix :
                IsPrefix
                  (ForwardOrderedProjections.frontierAt
                    c.core.T c.core.cut i).1 t.1 :=
              selectedFrontier_some_prefix c.core v.1 i hsel
            by_cases hsafe : InHomTree (k - (m + 1))
                (ForwardQActualCoordinateWord.tailOfTNode
                  c.core i t)
            · have hbudget :
                  SkewTree.heightAt c.core.T t.1 -
                    SkewTree.heightAt c.core.T
                      (ForwardOrderedProjections.frontierAt
                        c.core.T c.core.cut i).1 <
                    k - (m + 1) := by
                have hrank :=
                  tailOfTNode_length_eq_rank_diff c.core i t
                change (ForwardQActualCoordinateWord.tailOfTNode
                  c.core i t).length < k - (m + 1) at hsafe
                rw [hrank] at hsafe
                exact hsafe
              have hv : v = ambientAtTRoot c t.1 t.2 := by
                apply Subtype.ext
                rfl
              have hs : c.ambient.word s =
                  Sum.inr (ambientAtTRoot c t.1 t.2) := by
                rw [← hv]
                exact hf
              have houtside :
                  ∀ j : MixedProduct.BulletIndex (kind c.core),
                    gamma1 j = false →
                    ¬ IsPrefix
                      (markedProjection c.core
                        (ForwardQEnlargedConstantWords.eraseAux
                          c.core fallback x.1) j).1 t.1 := by
                intro j hj
                exact hexterior v hf j hj
              have hbridge :=
                ForwardQSafeFibreSmoothness.fibreQ_eq_on_safe_gamma2_exterior
                  hb c fallback x y gamma1 hxy i t hprefix
                  hbudget s hs houtside
              simpa only [fibreQStarredWord_symbol] using hbridge
            · exact ForwardQFibreDefaults.equal_on_unsafe_fibre
                c fallback x.1 y.1 s v hf hbefore i hsel hsafe

/-- With Gamma2 empty, the premise is automatic and the WHOLE
corrected fibrewise Q word is independent of selected marked points.
This recovers the word half of the B2-empty result uniformly from
the general exterior theorem and serves as a consistency check. -/
theorem starred_Q_word_eq_all_gamma1
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (fun _ => true) x.1 y.1)
    (s : BoundedNode b n) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  apply starred_Q_word_eq_of_root_gamma2_exterior
    hb c fallback x y (fun _ => true) hxy s
  intro v hv j hj
  simp at hj


/-- A marked Q cone that misses an AMBIENT occurrence also misses
the root of that occurrence's original f-variable fibre: the
original word's variable-root axiom puts the root below s.
Thus the root-exterior premise is not an additional hypothesis
when comparing words at the observable ambient positions of
Definition 24. -/
theorem root_exterior_of_ambient_position_exterior
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (s : BoundedNode b n)
    (houtside :
      ∀ j : MixedProduct.BulletIndex (kind c.core),
        gamma1 j = false →
        ¬ IsPrefix
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback x) j).1 s.1) :
    RootGamma2Exterior c fallback x gamma1 s := by
  intro v hv j hj hmarkerroot
  have hroots : IsPrefix v.1.1 s.1 :=
    c.ambient.below v s hv
  exact houtside j hj (isPrefix_trans hmarkerroot hroots)

/-- Definition 21 smoothness makes the ACTUAL finished Q words
equal at every ambient position outside the projected Gamma2
marked cones. Unlike the earlier safe-fibre theorem, this
assertion includes all default cases and all original positions
of each original f-variable fibre. -/
theorem starred_Q_word_eq_outside_gamma2_cones
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (s : BoundedNode b n)
    (houtside :
      ∀ j : MixedProduct.BulletIndex (kind c.core),
        gamma1 j = false →
        ¬ IsPrefix
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback x.1) j).1 s.1) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  exact starred_Q_word_eq_of_root_gamma2_exterior
    hb c fallback x y gamma1 hxy s
      (root_exterior_of_ambient_position_exterior
        c fallback x.1 gamma1 s houtside)

/-- The THREE concrete observables demanded by the source
Definition 24 simplicity test, indexed by the actual corrected
D2 / literal-R markers rather than yet asserting their
identification with the abstract canonical A-markers.

(1) the two Q trees have the same interior;
(2) every Gamma2 selected projected Q marked node is fixed;
(3) the COMPLETE decoded Q word agrees at every ambient
    position outside the union of those marked successor cones.

The remaining source-facing task is to identify the paper's
canonical A-to-R address correspondence. -/
theorem corrected_Q_simple_observables
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1) :
    (∀ t : Node b,
      t ∈ SkewTree.interior
        (fibreQStarredWord hb c fallback x).tree ↔
      t ∈ SkewTree.interior
        (fibreQStarredWord hb c fallback y).tree) ∧
    (∀ j : MixedProduct.BulletIndex (kind c.core),
      gamma1 j = false →
      markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1) j =
      markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux c.core fallback y.1) j) ∧
    (∀ s : BoundedNode b n,
      (∀ j : MixedProduct.BulletIndex (kind c.core),
        gamma1 j = false →
        ¬ IsPrefix
          (markedProjection c.core
            (ForwardQEnlargedConstantWords.eraseAux
              c.core fallback x.1) j).1 s.1) →
      (fibreQStarredWord hb c fallback x).word.word s =
        (fibreQStarredWord hb c fallback y).word.word s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ForwardQSimpleLetterSmooth.Q_interiors_eq
      hb c fallback x y t
  · intro j hj
    exact ForwardQAmbientFibreSmoothObservable.gamma2_Q_markedProjection_eq_of_smooth
      c fallback x y gamma1 hxy j hj
  · intro s houtside
    exact starred_Q_word_eq_outside_gamma2_cones
      hb c fallback x y gamma1 hxy s houtside

end DualTree.ForwardQAllExteriorFibres
