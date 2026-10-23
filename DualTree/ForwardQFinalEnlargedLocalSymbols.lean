import DualTree.ForwardQFinalReverseCoverageCriterion
import DualTree.ForwardQVisibleAncestorDecoder
import DualTree.ForwardQFinalLocalSymbolTransport

/-!
# Genuine enlarged-alphabet local symbol decoding for corrected Lemma 27

The source's smooth Ramsey step supplies a local mixed variable word
over the ENLARGED alphabet α ⊕ Fin(m+1). Its fixed auxiliary letters
cannot be treated as original-alphabet constants.

At each actual frontier coordinate i, a fixed auxiliary letter j
must be decoded by the already verified visible-ancestor map R_i.
If R_i(j) is an OLD source variable, it becomes the corresponding
genuine RETAINED root of the proposed final word, not a constant.
Original fixed letters remain constants. Actual local variable
symbols continue to map to their uniquely selected projected
final roots, with excluded top-level variables constantized.

The key geometric fact is that any old source root named by R_i
is a strict prefix of frontier i, hence of EVERY local projected
point P_i(z). Therefore this local decoder is root-compatible
for the original ambient variable word, including fixed auxiliary
letters. No Hall matching between independent local variables
and the old source roots is required or assumed.

This file gives the genuine local symbol/root interface. It does
NOT yet establish the full global f' word or the Ramsey theorem.
-/

namespace DualTree.ForwardQFinalEnlargedLocalSymbols

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalGlobalFibreSubstitution

/-- The actual auxiliary decoder R_i as a sum of original letters
and REAL retained FINAL variable roots. An old variable root is
kept as an independent final root, not evaluated prematurely. -/
noncomputable def decodeAuxIntoFinal
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (j : Fin (m + 1)) :
    Sum α (FinalRoot g f) :=
  Sum.map id
    (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot g f)
    (ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j)

/-- Genuine enlarged local interpolation at an actual safe
coordinate: original constants stay constants; auxiliary constants
are decoded by R_i to either original constants or retained old
variables; genuine local variables become their selected independent
projected final roots (and only budget-excluded roots are frozen). -/
noncomputable def enlargedLocalSymbol
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k - (m + 1))) :
    Sum α (FinalRoot g f) := by
  classical
  exact match (f.vector.components i).word z with
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr j) => decodeAuxIntoFinal g f fallback i j
  | Sum.inr v =>
      if hv : (⟨i, v.1⟩ : LocalAddress g.core) ∈
          selectedLocalRoots g.core f (m+q) then
        Sum.inr (selectedBoundedRoot g f ⟨⟨i,v.1⟩, hv⟩)
      else Sum.inl fallback

/-- The new local decoder interprets every genuine fixed
auxiliary word constant via R_i. In particular, such a symbol
is not spuriously required to be an original-alphabet constant. -/
theorem enlargedLocalSymbol_aux_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (j : Fin (m+1))
    (hword : (f.vector.components i).word z =
      Sum.inl (Sum.inr j)) :
    enlargedLocalSymbol g f fallback i z =
      decodeAuxIntoFinal g f fallback i j := by
  simp [enlargedLocalSymbol, hword]

/-- True local variable roots remain independently selected
global final roots when the target height budget retains them,
regardless of any fixed auxiliary constants elsewhere in
the local component word. -/
theorem enlargedLocalSymbol_at_selected_root
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (hselected :
      (⟨i,v.1⟩ : LocalAddress g.core) ∈
        selectedLocalRoots g.core f (m+q)) :
    enlargedLocalSymbol g f fallback i v.1 =
      Sum.inr (selectedBoundedRoot g f ⟨⟨i,v.1⟩,hselected⟩) := by
  have hroot :
      (f.vector.components i).word v.1 = Sum.inr v :=
    (f.vector.components i).toVariableWord.atRoot v
  simp [enlargedLocalSymbol, hroot, hselected]

/-- If R_i(j) is a genuine old source variable, its chosen
FINAL retained root is exactly that old bounded ambient node. -/
theorem oldSourceFinalRoot_underlying
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (v : g.core.source.word.Vars) :
    (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
      g f v).1.1 = v.1.1 := by
  change
    (ForwardQFinalEarlyFibreAssignment.earlyFinalRoot g f
      (ForwardQAmbientFibreFrame.ambientAtSourceRoot g v)
      (ForwardQAmbientFibreFrame.source_root_before_cut g v)).1.1 =
      v.1.1
  rw [ForwardQFinalEarlyFibreAssignment.earlyFinalRoot_val]
  rfl

/-- The enlarged decoder's most important safety property:
EVERY final variable emitted by an ACTUAL local word (whether
a local variable root or the decoding of a fixed auxiliary
constant) is rooted at a genuine PREFIX of P_i(z) in T. -/
theorem enlargedLocalSymbol_variable_below
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (v : FinalRoot g f)
    (hletter : enlargedLocalSymbol g f fallback i z =
      Sum.inr v) :
    IsPrefix v.1.1 (projected g.core ⟨i,z⟩).1 := by
  cases hw : (f.vector.components i).word z with
  | inl letter =>
      cases letter with
      | inl a =>
          simp [enlargedLocalSymbol, hw] at hletter
      | inr j =>
          cases hd :
              ForwardQVisibleAncestorDecoder.decodeAux
                g.core fallback i j with
          | inl a =>
              simp [enlargedLocalSymbol, decodeAuxIntoFinal,
                hw, hd] at hletter
          | inr old =>
              have hchosen :
                  ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
                    g f old = v := by
                have heq :
                    (Sum.inr
                      (ForwardQFinalReverseCoverageCriterion.oldSourceFinalRoot
                        g f old) : Sum α (FinalRoot g f)) =
                      Sum.inr v := by
                  simpa [enlargedLocalSymbol, decodeAuxIntoFinal,
                    hw, hd] using hletter
                exact Sum.inr.inj heq
              have hprefix :=
                ForwardQVisibleAncestorDecoder.decodeAux_variable_prefix
                  g.core fallback i j old hd
              have hcone : IsPrefix
                  (ForwardOrderedProjections.frontierAt
                    g.core.T g.core.cut i).1
                  (projected g.core ⟨i,z⟩).1 :=
                projected_cone g.core ⟨i,z⟩
              rw [← hchosen, oldSourceFinalRoot_underlying g f old]
              exact isPrefix_trans hprefix.1 hcone
  | inr old =>
      by_cases hs :
          (⟨i,old.1⟩ : LocalAddress g.core) ∈
            selectedLocalRoots g.core f (m+q)
      · have hchosen :
            selectedBoundedRoot g f ⟨⟨i,old.1⟩,hs⟩ = v := by
          have hsum :
              (Sum.inr (selectedBoundedRoot g f ⟨⟨i,old.1⟩,hs⟩) :
                Sum α (FinalRoot g f)) = Sum.inr v := by
            simpa [enlargedLocalSymbol, hw, hs] using hletter
          exact Sum.inr.inj hsum
        rw [← hchosen]
        exact selected_local_variable_prefix_projected
          g f i old z hw hs
      · simp [enlargedLocalSymbol, hw, hs] at hletter

end DualTree.ForwardQFinalEnlargedLocalSymbols
