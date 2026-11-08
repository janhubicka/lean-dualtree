import DualTree.ForwardQFinalGlobalEnlargedWord
import DualTree.CutPreservation

/-!
# Initial-root retention in the genuine enlarged final word

The corrected relative refinement must preserve every original ambient
support root at or before the distinguished cut, including roots that
are not variables of the old starred source word. These are precisely
the retained part of the final support construction.

This module exposes that property for the actual enlarged final word.
Together with its explicit syntactic substitution, root retention also
preserves every constant or root-labelled variable symbol at every
ambient position in the inclusive forward initial segment. No
alphabet-cardinality or positive-local-height assumption is needed.
-/

namespace DualTree.ForwardQFinalInitialRootRetention

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget
open ForwardQFinalGlobalEnlargedWord

/-- Every original ambient variable root at or before the inclusive
forward cut survives as a variable of the genuine enlarged final word.
This retains all early ambient roots, not only the old source variables. -/
theorem enlargedFinal_retains_initial_roots
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    u.1 ∈ (enlargedInterpolatedFinalWord g f fallback).support := by
  classical
  apply (enlargedInterpolatedFinalWord_support_iff g f fallback u.1).2
  change u.1.1 ∈ retained g.core ∪ selectedProjectedRoots g.core f (m+q)
  apply Finset.mem_union.mpr
  left
  change u.1.1 ∈ g.core.T.toFinset.filter (fun t => ForwardAux t g.core.cut)
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr ((g.ambient_support_T u.1).1 u.2), hbefore⟩

/-- On the entire inclusive forward initial segment, the final word
has the same constants and actual rooted variable symbols as the
original ambient word. Dependent variable membership proofs are erased
by `underlyingSymbol`, while the variable roots themselves are preserved. -/
theorem enlargedFinal_preserves_initial_symbols
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (s : BoundedNode b n)
    (hs : ForwardAux s.1 g.core.cut) :
    CutPreservation.underlyingSymbol
        (enlargedInterpolatedFinalWord g f fallback) s =
      CutPreservation.underlyingSymbol g.ambient s := by
  let cut : BoundedNode b n :=
    ⟨g.core.cut, g.T_bounded g.core.cut g.core.hcutT⟩
  apply CutPreservation.forwardCut_preserved_of_syntactic_refinement
    g.ambient (enlargedInterpolatedFinalWord g f fallback)
    (enlargedGlobalRootSymbol g f fallback) rfl cut ?_ s hs
  intro r hr hrcut
  exact enlargedFinal_retains_initial_roots
    g f fallback ⟨r, hr⟩ hrcut

end DualTree.ForwardQFinalInitialRootRetention
