import DualTree.Lemma27CanonicalColor
import DualTree.ForwardQFinalTargetExistence

/-!
# An inhabited canonical-signature fibre for the local colour step

The actual enlarged interpolation has a starred target with the source's
complete set signature precisely when its positive local height is at
least two.  This module expresses Track D's target-existence theorem in
the functional canonical-signature interface used by Track F.

In particular the empty-B₂ local colour step now gives an actual member
of the prescribed monochromatic signature fibre.  Nonemptiness of this
fibre is stronger than nonemptiness of the final evaluated span.  The
total smooth colour is still chosen before the local mixed word, and the
whole enlarged-span c-good witness is still a supplied input.
-/

namespace DualTree.Lemma27CanonicalWitness

open CorrectedTheoremSpec
open Lemma27CanonicalColor
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQEnlargedConstantWords
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalSyntacticSpanTransfer
open ForwardQFinalTargetExistence
open ForwardQSourceRefinement

/-- The prescribed canonical-signature fibre of the actual complete final
word is inhabited at local height at least two.  The witness satisfies both
syntactic word refinement and containment of its entire starred tree. -/
theorem canonicalSignature_fibre_nonempty
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α)
    (f : Corollary22CanonicalQ.EnlargedWord c.core q)
    (fallback : α) (hq : 0 < q) (hq2 : 2 ≤ q) :
    ∃ O : Starred b n l α,
      StarredBelow O (enlargedInterpolatedFinalKWord c f fallback hb hq) ∧
      canonicalSignature hb hl O = canonicalSignature hb hl c.core.source := by
  obtain ⟨O, hO⟩ := sourceRelativeSetTarget_nonempty hb c f fallback hq2
  exact ⟨O, (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
    (enlargedInterpolatedFinalKWord c f fallback hb hq) O).1 hO⟩

/-- Among positive local heights, the exact threshold for realizing the
source's canonical signature below the actual final word is two.  This
does not assert the existence of a local mixed Ramsey witness. -/
theorem canonicalSignature_fibre_nonempty_iff_two_le
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α)
    (f : Corollary22CanonicalQ.EnlargedWord c.core q)
    (fallback : α) (hq : 0 < q) :
    (∃ O : Starred b n l α,
      StarredBelow O (enlargedInterpolatedFinalKWord c f fallback hb hq) ∧
      canonicalSignature hb hl O = canonicalSignature hb hl c.core.source) ↔
      2 ≤ q := by
  constructor
  · rintro ⟨O, hO⟩
    exact (sourceRelativeSetTarget_nonempty_iff_two_le hb c f fallback hq).1
      ⟨O, (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
        (enlargedInterpolatedFinalKWord c f fallback hb hq) O).2 hO⟩
  · exact canonicalSignature_fibre_nonempty hb hl c f fallback hq

/-- The corrected empty-B₂ local canonization step, including an actual
starred member of its monochromatic prescribed-signature fibre.

The total smooth extension is chosen first, independently of any local
mixed word.  Every full-span c-good witness of intrinsic height at least
two gives a complete final refinement, the initial-root and rooted-symbol
retention contracts, and an inhabited monochromatic canonical fibre.
There is no two-letter alphabet assumption. -/
theorem exists_total_emptyBoundary_nonempty_fibre_canonization
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (color : StarredObservation b n α → γ)
    (hsimple : CanonicalTheoremSpec.SimpleWith
      (∅ : Set (CanonicalTheoremSpec.Boundary b l)) color) :
    let sig := canonicalSignature hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    ∃ total : EnlargedInput c.core → γ,
      (∀ w : EnlargedStarredInput c.core fallback,
        total w.1 = color (starredObserve (fibreQStarredWord hb c fallback w))) ∧
      (∀ x y : EnlargedInput c.core,
        MixedProduct.SmoothRelated (fun _ => true) x y → total x = total y) ∧
      ∀ (q : Nat) (f : Corollary22CanonicalQ.EnlargedWord c.core q),
        2 ≤ q → MixedProduct.Good total f →
        ∃ final : Word b n (m+q) α,
          SyntacticallyRefines final.toVariableWord c.ambient ∧
          (∀ u : c.ambient.Vars, ForwardAux u.1.1 c.core.cut →
            u.1 ∈ final.toVariableWord.support) ∧
          (∀ s : BoundedNode b n, ForwardAux s.1 c.core.cut →
            CutPreservation.underlyingSymbol final.toVariableWord s =
              CutPreservation.underlyingSymbol c.ambient s) ∧
          final.span.Nonempty ∧
          (∃ O : Starred b n l α,
            StarredBelow O final ∧ sig O = sig c.core.source) ∧
          Lemma28.FibreMonochromatic sig (fun O => color (starredObserve O))
            final (sig c.core.source) := by
  dsimp only
  have hsource := CanonicalTheoremSpec.sourceSimpleWithin_of_simpleWith
    c.ambient ∅ color hsimple
  obtain ⟨total, hagree, hsmooth, hmono⟩ :=
    Corollary22CanonicalQ.exists_total_emptyBoundary_Q_monochromatic
      hb c fallback fallbackColor (fun O => color (starredObserve O)) hsource
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hq hgood
  have hqpos : 0 < q := by omega
  refine ⟨enlargedInterpolatedFinalKWord c f fallback hb hqpos,
    enlargedFinal_syntacticallyRefines_ambient c f fallback,
    enlargedFinal_retains_initial_roots c f fallback,
    enlargedFinal_preserves_initial_symbols c f fallback,
    enlargedInterpolatedFinalKWord_span_nonempty c f fallback hb hqpos,
    canonicalSignature_fibre_nonempty hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
      c f fallback hqpos hq, ?_⟩
  exact fibreMonochromatic_of_Q_monochromatic hb
    (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    c f fallback hqpos color (hmono q f hq hgood)

end DualTree.Lemma27CanonicalWitness
