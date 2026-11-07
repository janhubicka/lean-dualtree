import DualTree.CanonicalPointReenumeration
import DualTree.Lemma27CanonicalWitness

/-!
# Canonical boundary colour control on the whole prescribed fibre

The selected-boundary reduction is transferred from actual Q outputs to
every eligible starred target with the source's complete set signature.
Track D supplies genuine Q preimages up to semantic observation, and
canonical-point invariance under support re-enumeration transports the
remaining selected boundary data through those preimages.

For every canonical-simple semantic colour, its total smooth Q extension
is chosen before the local mixed word.  Every full enlarged-span c-good
word of intrinsic dimension at least two gives an actual complete ambient
refinement with an inhabited prescribed signature fibre whose colours
depend only on the canonical B2 points.  Initial roots and rooted symbols
are retained through the inclusive forward cut.

For nonempty B2 this is colour factorization, not monochromaticity.  The
residual point-colour Ramsey refinement, existence of the c-good mixed
word, and final model-signature induction remain separate obligations.
-/

namespace DualTree.Lemma27CanonicalPointColor

open CorrectedTheoremSpec
open Lemma27CanonicalColor
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQEnlargedConstantWords
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalSyntacticSpanTransfer
open ForwardQFinalSetSpanTransfer
open ForwardQSourceRefinement

/-- On one eligible signature fibre, the selected canonical boundary
points contain all the remaining colour information. -/
def FibrePointCanonical
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) : Prop :=
  ∀ U V : Starred b n l α,
    StarredBelow U f → StarredBelow V f →
    signature U = s → signature V = s →
    (∀ a, a ∈ B2 →
      ForwardSemiCompleteSimplicity.canonicalPoint U a =
        ForwardSemiCompleteSimplicity.canonicalPoint V a) →
    color U = color V

/-- Further syntactic refinement preserves colour factorization on a
fixed ambient signature fibre.  No model-signature transport is implied. -/
theorem fibrePointCanonical_of_syntacticRefines
    {b n l k k' : Nat} {α γ Sig : Type*}
    {signature : Starred b n l α → Sig}
    {B2 : Set (CanonicalTheoremSpec.Boundary b l)}
    {color : Starred b n l α → γ}
    {f : Word b n k α} {g : Word b n k' α} {s : Sig}
    (hgf : KVariableWord.SyntacticRefines g f)
    (hcanonical : FibrePointCanonical signature B2 color f s) :
    FibrePointCanonical signature B2 color g s := by
  intro U V hU hV hsigU hsigV hpoints
  exact hcanonical U V
    (starredBelow_of_syntacticRefines hgf hU)
    (starredBelow_of_syntacticRefines hgf hV) hsigU hsigV hpoints

/-- With no selected boundary points, factorization is precisely
pairwise monochromaticity of the eligible signature fibre. -/
theorem fibrePointCanonical_empty_iff
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) :
    FibrePointCanonical signature ∅ color f s ↔
      Lemma28.FibreMonochromatic signature color f s := by
  constructor
  · intro h U V hU hV hsigU hsigV
    exact h U V hU hV hsigU hsigV (by intro a ha; cases ha)
  · intro h U V hU hV hsigU hsigV _
    exact h U V hU hV hsigU hsigV

/-- Semantic observation equality preserves every intrinsic boundary
point, even when the two support lists have different enumerations. -/
theorem canonicalPoint_eq_of_starredObserve_eq
    {b n l : Nat} {α : Type*}
    (hb : 0 < b) (U V : Starred b n l α)
    (h : starredObserve U = starredObserve V)
    (a : CanonicalTheoremSpec.Boundary b l) :
    ForwardSemiCompleteSimplicity.canonicalPoint U a =
      ForwardSemiCompleteSimplicity.canonicalPoint V a := by
  apply CanonicalPointReenumeration.canonicalPoint_eq_of_tree_toFinset_eq
    hb U V _ a
  exact congrArg Prod.fst h

/-- The genuine set-signature Q preimages transfer selected-boundary
colour control to the whole eligible fibre of the actual final word. -/
theorem fibrePointCanonical_of_Q_point_canonical
    {b n l k m q : Nat} {α γ : Type*}
    (hb : 0 < b) (hl : 0 < l)
    (c : FibreFrame b n l k m α)
    (f : Corollary22CanonicalQ.EnlargedWord c.core q)
    (fallback : α) (hq : 0 < q)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : StarredObservation b n α → γ)
    (hcanonical : ∀ x y : EnlargedStarredInput c.core fallback,
      x.1 ∈ f.span → y.1 ∈ f.span →
      (∀ a, a ∈ B2 →
        ForwardSemiCompleteSimplicity.canonicalPoint
            (fibreQStarredWord hb c fallback x) a =
          ForwardSemiCompleteSimplicity.canonicalPoint
            (fibreQStarredWord hb c fallback y) a) →
      color (starredObserve (fibreQStarredWord hb c fallback x)) =
        color (starredObserve (fibreQStarredWord hb c fallback y))) :
    FibrePointCanonical (canonicalSignature hb hl) B2
      (fun O => color (starredObserve O))
      (enlargedInterpolatedFinalKWord c f fallback hb hq)
      (canonicalSignature hb hl c.core.source) := by
  intro U V hU hV hsigU hsigV hpoints
  have hTargetU :=
    (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
      (enlargedInterpolatedFinalKWord c f fallback hb hq) U).2
      ⟨hU, hsigU⟩
  have hTargetV :=
    (sourceRelativeSetTarget_iff_starredBelow_signature hb hl c
      (enlargedInterpolatedFinalKWord c f fallback hb hq) V).2
      ⟨hV, hsigV⟩
  obtain ⟨x, hx, hQx⟩ :=
    sourceRelativeSetTarget_has_Q_preimage hb c f fallback U hTargetU
  obtain ⟨y, hy, hQy⟩ :=
    sourceRelativeSetTarget_has_Q_preimage hb c f fallback V hTargetV
  simp only [observe_eq_starredObserve] at hQx hQy
  have hQpoints : ∀ a, a ∈ B2 →
      ForwardSemiCompleteSimplicity.canonicalPoint
          (fibreQStarredWord hb c fallback x) a =
        ForwardSemiCompleteSimplicity.canonicalPoint
          (fibreQStarredWord hb c fallback y) a := by
    intro a ha
    exact (canonicalPoint_eq_of_starredObserve_eq hb _ U hQx a).trans
      ((hpoints a ha).trans
        (canonicalPoint_eq_of_starredObserve_eq hb _ V hQy a).symm)
  exact (congrArg color hQx).symm.trans
    ((hcanonical x y hx hy hQpoints).trans (congrArg color hQy))

/-- The corrected local factorization theorem for every canonical B2.

One total globally smooth colour is chosen first.  Each genuine mixed
word c-good on its full enlarged-alphabet span, with q at least two,
constructs a complete refinement and an inhabited prescribed-signature
fibre on which the selected canonical points determine the colour.
No target-coverage or target-colour hypothesis is supplied by the caller. -/
theorem exists_total_nonempty_fibre_point_canonization
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : StarredObservation b n α → γ)
    (hsimple : CanonicalTheoremSpec.SimpleWith B2 color) :
    let sig := canonicalSignature hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    ∃ total : EnlargedInput c.core → γ,
      (∀ w : EnlargedStarredInput c.core fallback,
        total w.1 = color (starredObserve (fibreQStarredWord hb c fallback w))) ∧
      (∀ x y : EnlargedInput c.core,
        MixedProduct.SmoothRelated
            (ForwardSemiCompleteSimplicity.gamma1OfBoundaryB2 hb c.core B2) x y →
          total x = total y) ∧
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
          FibrePointCanonical sig B2 (fun O => color (starredObserve O))
            final (sig c.core.source) := by
  dsimp only
  have hsource := CanonicalTheoremSpec.sourceSimpleWithin_of_simpleWith
    c.ambient B2 color hsimple
  obtain ⟨total, hagree, hsmooth, hcanonical⟩ :=
    Corollary22CanonicalQ.exists_total_simple_Q_point_canonization
      hb c fallback fallbackColor B2 (fun O => color (starredObserve O)) hsource
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hq hgood
  have hqpos : 0 < q := by omega
  refine ⟨enlargedInterpolatedFinalKWord c f fallback hb hqpos,
    enlargedFinal_syntacticallyRefines_ambient c f fallback,
    enlargedFinal_retains_initial_roots c f fallback,
    enlargedFinal_preserves_initial_symbols c f fallback,
    enlargedInterpolatedFinalKWord_span_nonempty c f fallback hb hqpos,
    Lemma27CanonicalWitness.canonicalSignature_fibre_nonempty hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
      c f fallback hqpos hq, ?_⟩
  exact fibrePointCanonical_of_Q_point_canonical hb
    (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    c f fallback hqpos B2 color (hcanonical q f hq hgood)

end DualTree.Lemma27CanonicalPointColor
