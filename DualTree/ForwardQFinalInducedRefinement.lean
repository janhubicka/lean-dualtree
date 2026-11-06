import DualTree.ForwardQAmbientFibreSpan
import DualTree.ForwardQFinalEnlargedWholeDomainEvaluation
import DualTree.ForwardQSourceRefinement

/-!
# The induced Q word is a syntactic refinement of the enlarged final word

Every assignment to the final roots gives an actual enlarged starred local
input. Its Q output factors symbolically through the enlarged interpolated
word: retained early roots use the original source substitution, while new
projected roots receive their chosen original-alphabet letters.

The factorization preserves all old source variables, including those
decoded from genuine fixed auxiliary letters. Budget-excluded local roots
and late ambient roots without a safe projection use the same fallback in
both constructions. Thus this is a whole-word syntactic refinement for any
alphabet, with no separation by evaluated assignments required.
-/

namespace DualTree.ForwardQFinalInducedRefinement

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSpan
open ForwardQAmbientFibreLegalWord
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalEarlyFibreAssignment
open ForwardQFinalReverseCoverageCriterion
open ForwardQFinalEnlargedLocalSymbols
open ForwardQFinalEnlargedInducedEvaluation
open ForwardQFinalEnlargedWholeDomainEvaluation
open ForwardQFinalSafeAddressLookup
open ForwardQSourceRefinement

private noncomputable def inducedRootSubstitution
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (σ : FinalRoot g f → α) :
    FinalRoot g f → Sum α g.core.source.word.Vars := by
  classical
  exact fun v =>
    if ForwardAux v.1.1 g.core.cut then
      g.substitution ⟨v.1, boundedFinalRoots_subset_original g f v⟩
    else Sum.inl (σ v)

private theorem inducedRootSubstitution_early
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (σ : FinalRoot g f → α)
    (u : g.ambient.Vars)
    (hbefore : ForwardAux u.1.1 g.core.cut) :
    inducedRootSubstitution g f σ (earlyFinalRoot g f u hbefore) =
      g.substitution u := by
  have horig :
      (⟨(earlyFinalRoot g f u hbefore).1,
        boundedFinalRoots_subset_original g f
          (earlyFinalRoot g f u hbefore)⟩ : g.ambient.Vars) = u :=
    Subtype.ext (earlyFinalRoot_val g f u hbefore)
  simp [inducedRootSubstitution, earlyFinalRoot_val, hbefore, horig]

private theorem inducedRootSubstitution_old
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (σ : FinalRoot g f → α)
    (v : g.core.source.word.Vars) :
    inducedRootSubstitution g f σ (oldSourceFinalRoot g f v) =
      Sum.inr v := by
  have hbefore :
      ForwardAux (ambientAtSourceRoot g v).1.1 g.core.cut := by
    simpa only [ambientAtSourceRoot] using source_root_before_cut g v
  exact (inducedRootSubstitution_early g f σ
    (ambientAtSourceRoot g v) hbefore).trans
      (source_substitution_fixes_old_root g v)

private theorem inducedRootSubstitution_selected
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (σ : FinalRoot g f → α)
    (u : SelectedTag g f) :
    inducedRootSubstitution g f σ (selectedBoundedRoot g f u) =
      Sum.inl (σ (selectedBoundedRoot g f u)) := by
  have hafter :
      ¬ ForwardAux (selectedBoundedRoot g f u).1.1 g.core.cut := by
    rw [selectedBoundedRoot_node]
    exact ForwardQFinalSupportCut.projected_outside_cut g.core u.1
  simp [inducedRootSubstitution, hafter]

private theorem inducedRootSubstitution_decodeAux
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core) (j : Fin (m+1)) :
    KVariableWord.mapSymbol (inducedRootSubstitution g f σ)
        (decodeAuxIntoFinal g f fallback i j) =
      ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j := by
  cases h : ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j with
  | inl a =>
      simp [decodeAuxIntoFinal, h, KVariableWord.mapSymbol]
  | inr v =>
      simp [decodeAuxIntoFinal, h, KVariableWord.mapSymbol,
        inducedRootSubstitution_old]

private theorem inducedRootSubstitution_local
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    KVariableWord.mapSymbol (inducedRootSubstitution g f σ)
        (enlargedLocalSymbol g f fallback i z) =
      match (enlargedInducedInput g f fallback σ).words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux g.core fallback i j := by
  classical
  rw [enlargedInducedInput_word_at]
  cases hw : (f.vector.components i).word z with
  | inl letter =>
      cases letter with
      | inl a =>
          simp [enlargedLocalSymbol, hw, SpanAudit.evalSymbol,
            KVariableWord.mapSymbol]
      | inr j =>
          simpa only [enlargedLocalSymbol, hw, SpanAudit.evalSymbol] using
            inducedRootSubstitution_decodeAux g f fallback σ i j
  | inr v =>
      by_cases hs : (⟨i,v.1⟩ : LocalAddress g.core) ∈
          selectedLocalRoots g.core f (m+q)
      · simp [enlargedLocalSymbol, hw, SpanAudit.evalSymbol,
          chosenLocalLetter, hs, KVariableWord.mapSymbol,
          inducedRootSubstitution_selected]
      · simp [enlargedLocalSymbol, hw, SpanAudit.evalSymbol,
          chosenLocalLetter, hs, KVariableWord.mapSymbol]

private theorem inducedRootSubstitution_global
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (u : g.ambient.Vars) :
    KVariableWord.mapSymbol (inducedRootSubstitution g f σ)
        (enlargedGlobalRootSymbol g f fallback u) =
      fibreSubstitution g fallback (enlargedInducedInput g f fallback σ) u := by
  by_cases hbefore : ForwardAux u.1.1 g.core.cut
  · rw [enlargedGlobalRootSymbol_early g f fallback u hbefore,
      fibreSubstitution_before_cut g fallback _ u hbefore]
    exact inducedRootSubstitution_early g f σ u hbefore
  · rw [fibreSubstitution_after_cut g fallback _ u hbefore]
    cases hsafe : safeAddress g.core u.1.1 with
    | none =>
        rw [enlargedGlobalRootSymbol_late_no_safe
          g f fallback u hbefore hsafe]
        have hQ := enlarged_Q_symbol_late_no_safe
          g fallback (enlargedInducedInput g f fallback σ)
          u u.1 (g.ambient.atRoot u) hbefore hsafe
        rw [ForwardQAmbientFibreSymbol.fibreQ_after_cut
          g fallback _ u.1 u (g.ambient.atRoot u) hbefore] at hQ
        exact hQ.symm
    | some a =>
        rcases a with ⟨i,z⟩
        have hu :
            ambientAtTRoot g (projected g.core ⟨i,z⟩).1
              (projected g.core ⟨i,z⟩).2 = u := by
          apply Subtype.ext
          apply Subtype.ext
          exact safeAddress_spec g.core u.1.1 ⟨i,z⟩ hsafe
        have hglobal : enlargedGlobalRootSymbol g f fallback u =
            enlargedLocalSymbol g f fallback i z := by
          rw [← hu]
          exact enlargedGlobalRootSymbol_projected g f fallback i z
        have hdecode :
            ForwardQAmbientFibreSymbol.decodeAmbientRoot g fallback
                (enlargedInducedInput g f fallback σ) u =
              match (enlargedInducedInput g f fallback σ).words i z with
              | Sum.inl a => Sum.inl a
              | Sum.inr j =>
                  ForwardQVisibleAncestorDecoder.decodeAux
                    g.core fallback i j := by
          rw [← hu]
          exact ForwardQAmbientFibreSymbol.decode_ambient_projected_root
            g fallback (enlargedInducedInput g f fallback σ) i z
        rw [hglobal, hdecode]
        exact inducedRootSubstitution_local g f fallback σ i z

private theorem inducedQ_word_eq_substitute
    {b n l k m q : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α) :
    ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (enlargedInducedInput g f fallback σ) =
      SpanAudit.substitute (enlargedInterpolatedFinalWord g f fallback).word
        (inducedRootSubstitution g f σ) := by
  rw [fibreQSymbol_eq_substitute]
  change SpanAudit.substitute g.ambient.word
      (fibreSubstitution g fallback (enlargedInducedInput g f fallback σ)) =
    SpanAudit.substitute
      (SpanAudit.substitute g.ambient.word (enlargedGlobalRootSymbol g f fallback))
      (inducedRootSubstitution g f σ)
  rw [KVariableWord.substitute_compose]
  apply congrArg (SpanAudit.substitute g.ambient.word)
  funext u
  exact (inducedRootSubstitution_global g f fallback σ u).symm

/-- The actual induced enlarged starred Q output syntactically refines
the interpolated final word for every final-root assignment. All source
variables and fixed auxiliary-letter decodings are preserved; the claim
holds for arbitrary alphabets without an evaluated-span hypothesis. -/
theorem inducedQ_syntacticallyRefines_final
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (σ : FinalRoot g f → α)
    (hq : 0 < q) :
    SyntacticallyRefines
      (fibreQStarredWord hb g fallback
        (enlargedInducedStarredInput g f fallback σ hq)).word
      (enlargedInterpolatedFinalWord g f fallback) := by
  change ∃ ρ : FinalRoot g f → Sum α g.core.source.word.Vars,
    ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback (enlargedInducedInput g f fallback σ) =
      SpanAudit.substitute (enlargedInterpolatedFinalWord g f fallback).word ρ
  exact ⟨inducedRootSubstitution g f σ,
    inducedQ_word_eq_substitute g f fallback σ⟩

end DualTree.ForwardQFinalInducedRefinement
