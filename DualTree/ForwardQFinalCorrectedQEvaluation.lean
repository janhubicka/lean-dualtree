import DualTree.ForwardQFinalFibreEvaluation
import DualTree.ForwardQMixedSpanEvaluation

/-!
# Compare interpolated ambient f' with the corrected Q map at P_i(z)

The genuinely constructed ambient f' has final (m+q)-complete
skew support, exactly the selected variable roots, and span
contained in the original ambient f. Its evaluation on every
original ambient fibre rooted at P_i(z) is the local component
evaluation under the induced selected-variable assignment.

For ANY final variable assignment sigma, its induced coordinate
words form a member of the actual vector-variable-word span.
If a full mixed-product point x has precisely those word
coordinates and satisfies the verified corrected starred
input condition, the actual source-facing Q(x) emits at
P_i(z) exactly the evaluated f' letter.

This statement works on ALL sorted D0/D2 frontiers and does
not need injective matching into the old source starred roots.
It deliberately does not claim that every induced vector-span
point has a legal starred D2-point extension, nor does it
prove Definition 24 simplicity or original reverse-starred W_*.
-/

namespace DualTree.ForwardQFinalCorrectedQEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalFibreEvaluation

/-- The coordinate words induced by a global final-variable
assignment are the ACTUAL local component evaluations of the
verified mixed variable word, with the excluded final-rank
variables fixed to fallback. -/
noncomputable def inducedCoordinates
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α) :
    Fin (ForwardSortedFrontiers.frontiers g.core.T g.core.cut).length →
      TreeWord b (k-(m+1)) α :=
  fun i => SpanAudit.eval (f.vector.components i).word
    (localAssignment g f fallback σ i)

/-- The induced coordinate-word family lies in the genuine
vector-product span, with an independently chosen assignment
for each sorted frontier index. This checks the word component
without fabricating D2 bullet-point choices or W_* conditions. -/
theorem inducedCoordinates_mem_vector_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α) :
    inducedCoordinates g f fallback σ ∈ f.vector.span := by
  intro i
  exact ⟨localAssignment g f fallback σ i, rfl⟩

/-- If a genuinely STARRED mixed point has the induced word
coordinates, then the TRUE corrected Q(x) symbol at each safe
P_i(z) equals the CONSTANT carrying the evaluation of the
constructed final ambient f' at that original ambient root.

The Q output still names the OLD source variables; evaluating
f' introduces new FINAL support variables. They are compared
only after f' evaluation, as their types require. -/
theorem corrected_Q_projected_agrees_with_final_eval
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (σ : FinalRoot g f → α)
    (x : ForwardQActualStarredSpace.StarredInput g.core)
    (hx : ∀ i : Index g.core,
      x.1.words i = inducedCoordinates g f fallback σ i)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    ((ForwardQActualCoordinateWord.coordinateConeData
        g.core x.1 fallback).onActualStarredQ
          hb g.core x g.T_bounded).word.word
      (ForwardQActualCoordinateWord.projectedBounded
        g.core g.T_bounded i z) =
    Sum.inl
      (SpanAudit.evalSymbol σ
        ((interpolatedFinalWord
          g f (fun a : α => a) fallback).word
          (ForwardQAmbientFibreFrame.ambientAtTRoot g
            (projected g.core ⟨i,z⟩).1
            (projected g.core ⟨i,z⟩).2).1)) := by
  have hQ :=
    ForwardQActualCoordinateWord.coordinateConeData_Q_symbol_projected
      hb g.core x fallback g.T_bounded i z
  rw [hQ]
  have hcoordinate :
      x.1.words i z =
        SpanAudit.eval (f.vector.components i).word
          (localAssignment g f fallback σ i) z :=
    congrFun (hx i) z
  rw [hcoordinate]
  have hword :=
    interpolatedFinalWord_projected_root_symbol
      g f (fun a : α => a) fallback i z
  rw [hword]
  have hEval := localSymbol_eval g f fallback σ i z
  exact congrArg
    (fun a : α => (Sum.inl a :
      Sum α g.core.source.word.Vars)) hEval.symm

end DualTree.ForwardQFinalCorrectedQEvaluation
