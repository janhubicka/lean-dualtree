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

end DualTree.ForwardQAllExteriorFibres
