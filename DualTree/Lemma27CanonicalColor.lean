import DualTree.CanonicalTheoremSpec
import DualTree.Corollary22CanonicalQ
import DualTree.ForwardQFinalSetSpanTransfer
import DualTree.ForwardAuxFiniteMaximum

/-!
# An actual fixed-signature canonization step for empty B₂

The corrected complete set signature is now a function on every starred
object with positive interior count: its cut is the unique maximal
interior vertex in the forward auxiliary order.  This removes the free
cut and literal-list choices from the fibre used by the finite induction.

For a semantic colour simple with empty canonical B₂, choose the total
globally smooth enlarged-Q extension FIRST.  Every genuine full-span
c-good local mixed word of intrinsic height at least two then constructs
the actual complete final word, retaining the original initial roots and
symbols, whose ENTIRE fixed-signature fibre is monochromatic.  The proof
uses Track D's proved Q preimages, not a coverage hypothesis supplied by
the caller.  It works over nonempty unary alphabets as well.

This is the empty-B₂ local colour step.  Mixed Ramsey existence, residual
point homogenization for nonempty B₂, the increasing-cut model-signature
transport, and the l=0 induction base are not supplied by this module.
-/

namespace DualTree.Lemma27CanonicalColor

open CorrectedTheoremSpec
open ForwardQFinalSetSignature
open ForwardQFinalSetSpanTransfer
open ForwardQFinalSyntacticSpanTransfer
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalInitialRootRetention
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQEnlargedConstantWords
open ForwardQSourceRefinement

/-- The corrected signature retains the whole optional rooted partial
word, including its strict domain, and the finite signature-node set. -/
abbrev Signature (b n : Nat) (α : Type*) :=
  Finset (Node b) ×
    (BoundedNode b n → Option (Sum α (BoundedNode b n)))

private theorem exists_lastInterior
    {b n l : Nat} {α : Type*}
    (hl : 0 < l) (O : Starred b n l α) :
    ∃ cut : Node b, cut ∈ SkewTree.interior O.tree ∧
      ∀ t, t ∈ SkewTree.interior O.tree →
        SkewTree.forwardAuxB t cut = true := by
  have hne : SkewTree.interior O.tree ≠ [] := by
    intro h
    have hc := O.interior_card
    rw [h] at hc
    simp only [List.length_nil] at hc
    omega
  obtain ⟨cut, hcut, hmax⟩ :=
    ForwardAuxFiniteMaximum.exists_maximal (SkewTree.interior O.tree) hne
  refine ⟨cut, hcut, ?_⟩
  intro t ht
  simpa only [SkewTree.forwardAuxB, decide_eq_true_eq] using hmax t ht

/-- The unique maximal interior vertex of a positive-interior starred
object, with respect to the corrected forward order. -/
noncomputable def lastInterior
    {b n l : Nat} {α : Type*}
    (hl : 0 < l) (O : Starred b n l α) : Node b :=
  Classical.choose (exists_lastInterior hl O)

theorem lastInterior_mem
    {b n l : Nat} {α : Type*}
    (hl : 0 < l) (O : Starred b n l α) :
    lastInterior hl O ∈ SkewTree.interior O.tree :=
  (Classical.choose_spec (exists_lastInterior hl O)).1

theorem lastInterior_maximal
    {b n l : Nat} {α : Type*}
    (hl : 0 < l) (O : Starred b n l α) :
    ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t (lastInterior hl O) = true :=
  (Classical.choose_spec (exists_lastInterior hl O)).2

/-- Any certified maximal interior cut equals the selected cut.  Thus
the choice does not add data to the mathematical signature. -/
theorem lastInterior_eq_of_maximal
    {b n l : Nat} {α : Type*}
    (hl : 0 < l) (O : Starred b n l α)
    (cut : Node b) (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true) :
    lastInterior hl O = cut := by
  apply CanonicalForwardAuxIso.forwardAux_antisymm
  · simpa only [SkewTree.forwardAuxB, decide_eq_true_eq] using
      hmax (lastInterior hl O) (lastInterior_mem hl O)
  · simpa only [SkewTree.forwardAuxB, decide_eq_true_eq] using
      lastInterior_maximal hl O cut hcut

/-- A genuine set-signature map on the full positive-interior starred
domain, with no caller-chosen cut or tree enumeration in its codomain. -/
noncomputable def canonicalSignature
    {b n l : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l) (O : Starred b n l α) :
    Signature b n α :=
  completeSetSignature hb O (lastInterior hl O)
    (lastInterior_mem hl O) (lastInterior_maximal hl O)

/-- The functional signature agrees with the existing geometric
signature at every certified maximal interior cut. -/
theorem canonicalSignature_eq_at_cut
    {b n l : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l) (O : Starred b n l α)
    (cut : Node b) (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true) :
    canonicalSignature hb hl O =
      completeSetSignature hb O cut hcut hmax := by
  have h := lastInterior_eq_of_maximal hl O cut hcut hmax
  subst cut
  rfl

/-- The geometric fixed-signature certificate is precisely equality
of the functional signatures; no new geometric premise is imposed. -/
theorem sameCompleteSetSignature_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α) (O : Starred b n l α) :
    (∃ cut, SameCompleteSetForwardSignature hb c O cut) ↔
      canonicalSignature hb hl O = canonicalSignature hb hl c.core.source := by
  constructor
  · rintro ⟨cut, H⟩
    rw [canonicalSignature_eq_at_cut hb hl O cut H.cutInterior H.cutMaximal,
      canonicalSignature_eq_at_cut hb hl c.core.source c.core.cut
        c.core.hcut c.core.hmax]
    exact H.signatureEq
  · intro h
    refine ⟨lastInterior hl O, lastInterior_mem hl O,
      lastInterior_maximal hl O, ?_⟩
    change canonicalSignature hb hl O = _
    exact h.trans (canonicalSignature_eq_at_cut hb hl c.core.source
      c.core.cut c.core.hcut c.core.hmax)

/-- Track D's actual target class is exactly the eligible fixed fibre
of the signature used by the finite canonization interface. -/
theorem sourceRelativeSetTarget_iff_starredBelow_signature
    {b n l k m p : Nat} {α : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α)
    (final : Word b n p α) (O : Starred b n l α) :
    SourceRelativeSetTarget hb c final.toVariableWord O ↔
      StarredBelow O final ∧
        canonicalSignature hb hl O = canonicalSignature hb hl c.core.source := by
  constructor
  · rintro ⟨cut, H, hRef, hTree⟩
    exact ⟨⟨hTree, hRef⟩, (sameCompleteSetSignature_iff hb hl c O).1 ⟨cut, H⟩⟩
  · rintro ⟨⟨hTree, hRef⟩, hSignature⟩
    obtain ⟨cut, H⟩ := (sameCompleteSetSignature_iff hb hl c O).2 hSignature
    exact ⟨cut, H, hRef, hTree⟩

/-- The corrected Q observation and the theorem-level semantic
observation retain definitionally the same finite set and rooted word. -/
theorem observe_eq_starredObserve
    {b n l : Nat} {α : Type*} (O : Starred b n l α) :
    ForwardQFinalTargetObservation.observe O = starredObserve O := by
  unfold ForwardQFinalTargetObservation.observe starredObserve
  apply Prod.ext
  · rfl
  · funext s
    simp only [ForwardQSimpleLetterSmooth.rootLabel,
      CutPreservation.underlyingSymbol]

/-- The proved genuine Q preimages transfer monochromaticity of its
starred span image to the WHOLE actual fixed-signature target fibre. -/
theorem fibreMonochromatic_of_Q_monochromatic
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α)
    (f : Corollary22CanonicalQ.EnlargedWord c.core q)
    (fallback : α) (hq : 0 < q)
    (color : StarredObservation b n α → γ)
    (hmono : ∀ x y : EnlargedStarredInput c.core fallback,
      x.1 ∈ f.span → y.1 ∈ f.span →
      color (starredObserve (fibreQStarredWord hb c fallback x)) =
        color (starredObserve (fibreQStarredWord hb c fallback y))) :
    Lemma28.FibreMonochromatic (canonicalSignature hb hl)
      (fun O => color (starredObserve O))
      (enlargedInterpolatedFinalKWord c f fallback hb hq)
      (canonicalSignature hb hl c.core.source) := by
  intro U V hU hV hSignatureU hSignatureV
  have hTargetU :=
    (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
      (enlargedInterpolatedFinalKWord c f fallback hb hq) U).2
      ⟨hU, hSignatureU⟩
  have hTargetV :=
    (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
      (enlargedInterpolatedFinalKWord c f fallback hb hq) V).2
      ⟨hV, hSignatureV⟩
  obtain ⟨x, hx, hQx⟩ :=
    sourceRelativeSetTarget_has_Q_preimage hb c f fallback U hTargetU
  obtain ⟨y, hy, hQy⟩ :=
    sourceRelativeSetTarget_has_Q_preimage hb c f fallback V hTargetV
  simp only [observe_eq_starredObserve] at hQx hQy
  exact (congrArg color hQx).symm.trans
    ((hmono x y hx hy).trans (congrArg color hQy))

/-- The empty-B₂ corrected local canonization step on actual words.

The total smooth colouring is chosen from the original simple colour
before any local mixed word.  A full-span c-good witness of dimension
q≥2 produces a complete final refinement, retains every source root and
symbol through the cut, and canonizes the complete set-signature fibre.
The c-good witness remains input; Q coverage and the colour conclusion
are proved.  No two-letter hypothesis is used. -/
theorem exists_total_emptyBoundary_fibre_canonization
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
    enlargedInterpolatedFinalKWord_span_nonempty c f fallback hb hqpos, ?_⟩
  exact fibreMonochromatic_of_Q_monochromatic hb
    (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    c f fallback hqpos color (hmono q f hq hgood)

end DualTree.Lemma27CanonicalColor
