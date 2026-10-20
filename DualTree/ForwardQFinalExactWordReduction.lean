import DualTree.ForwardQFinalFullSignatureRootTransport
import DualTree.ForwardQAmbientFibreSymbol

/-!
# Exact corrected Q-word comparison reduces to original ambient-f roots

The actual fibrewise Q uses the OLD source variable-root type.  An output
starred refinement O carries its OWN dependent variable-root type.
Under equality of complete corrected signatures these types are
canonically equivalent by identical bounded roots, but are not
definitionally identical.

The genuine Q word is syntactically uniform on each original ambient
f-variable fibre.  If O refines the final complete-skew ambient f' span
over an alphabet with two letters, the independently verified
SpanAudit uniformity theorem also forces O's ACTUAL word symbols
to be constant on each such original f-fibre.  Both preserve ambient
constants.

Therefore equality of the two dependent variable words, after the
canonical root reindexing, is equivalent to equality at the finite
original f-root set.  Moreover the complete signature supplies those
equalities automatically on EVERY early root, including the cut.

Only the genuinely LATE ambient f-variable root symbols remain to be
matched.  In the future these will be reconstructed by the corrected
D0/D2 local word coordinates and visible-ancestor auxiliary decoder.
No equality of full starred trees or existence of that late symbol
reconstruction is claimed here.
-/

namespace DualTree.ForwardQFinalExactWordReduction

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalFullSignatureRootTransport
open ForwardQFinalFullSignature

/-- Any starred output refining the final f' span also refines
the ORIGINAL ambient f evaluated span.  This is a genuine
transitive span inclusion rather than a guessed syntactic map. -/
theorem output_span_subset_original_ambient
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hspan :
      O.word.span ⊆
        (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
          g f (fun x : α => x) fallback).span) :
    O.word.span ⊆ g.ambient.span :=
  fun ψ hψ =>
    (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord_span_subset
      g f (fun x : α => x) fallback) (hspan hψ)

/-- The actual corrected Q word and an output with the same
complete signature have automatically matching rooted symbols
on ALL EARLY original f-variables, including the cut itself.
The actual variable root equivalence is NOT chosen arbitrarily. -/
theorem actual_Q_matches_output_on_early_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (u : g.ambient.Vars)
    (hu : ForwardAux u.1.1 g.core.cut) :
    Sum.map id
      (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1) = O.word.word u.1 := by
  have hQ :
      ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1 =
      g.core.source.word.word u.1 :=
    ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback w u.1 u (g.ambient.atRoot u) hu
  rw [hQ]
  by_cases hcut : u.1.1 = g.core.cut
  · have hsourceRoot :
        u.1 ∈ g.core.source.word.support := by
      apply ForwardQFinalConcreteSignature.mem_support_of_mem_supportNodes
        g.core.source.word u.1
      apply (g.core.source.support_eq_interior u.1.1).2
      simpa only [hcut] using g.core.hcut
    let v : g.core.source.word.Vars := ⟨u.1,hsourceRoot⟩
    exact root_reindexed_word_eq hb g O cutO H v
  · exact strict_prefix_reindexed_word_eq
      hb g O cutO H u.1 ⟨hu,hcut⟩

/-- Over a two-letter alphabet, the actual Q word equals O's
ACTUAL dependent word symbol function after canonical root
reindexing, provided it agrees at every original ambient
f-variable root.  Agreement at arbitrary homogeneous positions
then follows automatically from original f-fibre uniformity. -/
theorem actual_Q_word_eq_of_original_f_root_agreement
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan :
      O.word.span ⊆
        (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
          g f (fun x : α => x) fallback).span)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (hroots :
      ∀ u : g.ambient.Vars,
        Sum.map id
          (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w u.1) = O.word.word u.1)
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w s) = O.word.word s := by
  let e := sourceOutputVarsEquiv hb g O cutO H
  have hOrig : O.word.span ⊆ g.ambient.span :=
    output_span_subset_original_ambient g f fallback O hspan
  cases hs : g.ambient.word s with
  | inl a =>
      have hQ :
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s = Sum.inl a :=
        ForwardQAmbientFibreSymbol.fibreQ_original_constant
          g fallback w s a hs
      have hO : O.word.word s = Sum.inl a :=
        SpanAudit.constant_preserved_of_span_subset
          hα g.ambient.word O.word.word hOrig hs
      simp [hQ,hO]
  | inr u =>
      have hQ :
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s =
          ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w u.1 :=
        ForwardQAmbientFibreSymbol.fibreQ_constant_on_ambient_fibre
          g fallback w u s u.1 hs (g.ambient.atRoot u)
      have hO : O.word.word s = O.word.word u.1 :=
        SpanAudit.fibre_uniform_of_span_subset
          hα g.ambient.word O.word.word hOrig hs (g.ambient.atRoot u)
      calc
        Sum.map id e
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w s) =
          Sum.map id e
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w u.1) := congrArg (Sum.map id e) hQ
        _ = O.word.word u.1 := hroots u
        _ = O.word.word s := hO.symm

/-- It is enough to construct exact Q/O root-symbol equality
ONLY on late original f roots.  The full corrected signature
handles all early roots, while original-f fibre uniformity and
constant preservation handle every other ambient position. -/
theorem actual_Q_word_eq_of_late_root_agreement
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan :
      O.word.span ⊆
        (ForwardQFinalGlobalFibreSubstitution.interpolatedFinalWord
          g f (fun x : α => x) fallback).span)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (hlate :
      ∀ u : g.ambient.Vars,
        ¬ ForwardAux u.1.1 g.core.cut →
        Sum.map id
          (sourceOutputVarsEquiv hb g O cutO H)
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w u.1) = O.word.word u.1)
    (s : BoundedNode b n) :
    Sum.map id (sourceOutputVarsEquiv hb g O cutO H)
      (ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w s) = O.word.word s := by
  apply actual_Q_word_eq_of_original_f_root_agreement
    hb g f fallback O cutO H hα hspan w
  · intro u
    by_cases hu : ForwardAux u.1.1 g.core.cut
    · exact actual_Q_matches_output_on_early_root
        hb g O cutO H fallback w u hu
    · exact hlate u hu

end DualTree.ForwardQFinalExactWordReduction
