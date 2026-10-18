import DualTree.ForwardQFinalCorrectedQEvaluation
import DualTree.ForwardQFinalLocalRoots
import DualTree.ForwardQActualStarredSpace
import DualTree.ForwardSortedMixedProduct

/-!
# A genuine corrected starred mixed point for EVERY final assignment

For each global assignment to the selected final roots, the
corresponding independent coordinate word evaluations lie in the
actual vector span of the post-Ramsey mixed variable word f.
The missing D₂ point choices can be made canonically: use the
unique intrinsic-rank-zero root of each local component support.

The full vector-q-completeness axiom orders the ambient lengths
of these local roots at equal intrinsic rank zero, in the TRUE
sorted frontier index order. Therefore the chosen D₂ points
satisfy the genuine corrected BulletLengthsOrdered predicate and
define an actual StarredInput of the repaired Q map.

There are no D₁/up coordinates in this corrected source-facing
mixed kind: the impossible upPoint constructor is eliminated by
the already verified kind_ne_up theorem, not by an axiom.

Consequently every global final assignment yields an actual
corrected W_* point IN THE MIXED VARIABLE WORD'S SPAN. Applying
the previously checked corrected-Q comparison now proves
equality of Q(x_sigma) and the evaluated ambient f' at every
safe projected root P_i(z), unconditionally on additional
chosen bullet markers.

The remaining comparison at nonprojected ambient fibres and
Definition 24 simplicity/Ramsey transfer are independent.
The printed reverse-lex W_* is NOT identified here.
-/

namespace DualTree.ForwardQFinalInducedStarredPoint

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalFibreEvaluation
open ForwardQFinalCorrectedQEvaluation

/-- For ANY global final-variable assignment, choose the
actual local component evaluation at each sorted frontier,
and the intrinsic-zero support root at each genuine D₂
coordinate. No D₁ coordinate can exist. -/
noncomputable def inducedPoint
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α) :
    Input g.core where
  words := inducedCoordinates g f fallback σ
  upPoint := fun i =>
    False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  bulletPoint := fun i =>
    ForwardQFinalLocalRoots.localRoot g.core f i.1

/-- The canonically assembled actual mixed-product input lies
in the ENTIRE mixed variable word span, not just its vector
coordinate projection; the D₂ values really belong to local
supports, and the D₁ requirement is vacuous by proof. -/
theorem inducedPoint_mem_mixed_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α) :
    inducedPoint g f fallback σ ∈ f.span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨localAssignment g f fallback σ i, rfl⟩
  · intro i
    exact False.elim
      ((ForwardSortedMixedProduct.kind_ne_up
        g.core.source g.core.cut g.core.hcut g.core.hmax
        g.core.hout g.core.T g.core.hcomplete g.core.hnon
        g.core.hST g.core.hcutT g.core.hearly i.1) i.2)
  · intro i
    exact ForwardQFinalLocalRoots.localRoot_mem g.core f i.1

/-- For q>0 the intrinsic-rank-zero local roots are ambient-
length ordered on the TRUE D₂ subtype, as demanded by the
corrected W_* singleton-vector condition. -/
theorem inducedPoint_bullet_lengths_ordered
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    ForwardQIndexedTRanks.BulletLengthsOrdered
      g.core (inducedPoint g f fallback σ) := by
  intro i j hij
  change (ForwardQFinalLocalRoots.localRoot g.core f i.1).1.length ≤
    (ForwardQFinalLocalRoots.localRoot g.core f j.1).1.length
  let z := ForwardQFinalLocalRoots.localRoot g.core f i.1
  let w := ForwardQFinalLocalRoots.localRoot g.core f j.1
  have hz :
      z.1 ∈ (f.vector.components i.1).toVariableWord.supportNodes := by
    change z.1 ∈ (f.vector.components i.1).support.map
      (fun u => u.1)
    exact List.mem_map.mpr
      ⟨z,ForwardQFinalLocalRoots.localRoot_mem g.core f i.1,rfl⟩
  have hw :
      w.1 ∈ (f.vector.components j.1).toVariableWord.supportNodes := by
    change w.1 ∈ (f.vector.components j.1).support.map
      (fun u => u.1)
    exact List.mem_map.mpr
      ⟨w,ForwardQFinalLocalRoots.localRoot_mem g.core f j.1,rfl⟩
  exact ForwardQFinalVectorOrdering.local_lengths_le_of_equal_level
    g.core f i.1 j.1 hij 0 hq z w hz hw
    (ForwardQFinalLocalRoots.localRoot_height_zero g.core f i.1)
    (ForwardQFinalLocalRoots.localRoot_height_zero g.core f j.1)

/-- Every final-variable assignment determines a GENUINE
corrected starred input for Q, with no additional bullet-point
existence or order assumptions. -/
noncomputable def inducedStarredInput
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    ForwardQActualStarredSpace.StarredInput g.core :=
  ForwardQActualStarredSpace.starredInputOfOrdered
    g.core (inducedPoint g f fallback σ)
    (inducedPoint_bullet_lengths_ordered
      g f fallback σ hq)

/-- The actual corrected starred input is also an ACTUAL
member of the original post-Ramsey mixed variable-word
span, for every assignment to selected final variables. -/
theorem inducedStarredInput_mem_mixed_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    (inducedStarredInput g f fallback σ hq).1 ∈ f.span :=
  inducedPoint_mem_mixed_span g f fallback σ

/-- No conditional W_* witness remains: the ACTUAL corrected
Q on the canonically assembled mixed-span point has at every
genuine shortened projected ambient T root the same letter as
the evaluated constructed final ambient f'. -/
theorem corrected_Q_induced_projected_eval
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    ((ForwardQActualCoordinateWord.coordinateConeData
        g.core (inducedStarredInput g f fallback σ hq).1
        fallback).onActualStarredQ
          hb g.core (inducedStarredInput g f fallback σ hq)
          g.T_bounded).word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    Sum.inl
      (SpanAudit.evalSymbol σ
        ((interpolatedFinalWord
          g f (fun a : α => a) fallback).word
          (ForwardQAmbientFibreFrame.ambientAtTRoot g
            (projected g.core ⟨i,z⟩).1
            (projected g.core ⟨i,z⟩).2).1)) := by
  exact corrected_Q_projected_agrees_with_final_eval
    hb g f fallback σ
    (inducedStarredInput g f fallback σ hq)
    (fun i => rfl) i z

end DualTree.ForwardQFinalInducedStarredPoint
