import DualTree.MixedSupportThinning
import DualTree.Corollary22ResidualPoints
import DualTree.Lemma27CanonicalWitness

/-!
# From ordered residual-point selection to an inhabited canonical fibre

The remaining local Ramsey input is separated into actual support geometry.
Starting with one genuine full-span c-good mixed word, select a full
vector-complete family of support subsets.  Uniform root freezing builds
a smaller mixed word, with coordinatewise syntactic refinement, mixed span
inclusion, and inherited c-goodness.

The residual colour needs to be homogeneous only on the ordered D₂ point
tuples in those selected supports.  This is the exact corrected starred
Q-domain condition; no homogeneity on unordered Cartesian tuples is
required.  Only the Γ₂ restriction of each tuple is passed to the colour.

The final complete word is constructed directly from the smaller mixed
word.  At intrinsic height at least two it retains the original initial
roots and symbols, has an actual starred object with the source's complete
canonical signature, and makes that entire prescribed fibre monochromatic.
No refinement relation between two separately interpolated final words is
assumed.  Selecting the homogeneous vector supports and constructing the
initial c-good word remain genuine Ramsey obligations.
-/

namespace DualTree.Lemma27ResidualRefinement

open CorrectedTheoremSpec
open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQEnlargedConstantWords
open ForwardQFinalEnlargedCompleteWord
open ForwardQFinalInitialRootRetention
open ForwardQFinalSyntacticSpanTransfer
open ForwardQSourceRefinement
open Lemma27CanonicalColor

/-- A family of actual bounded local support lists at every frontier
coordinate, including the unmarked D₀ coordinates. -/
abbrev Supports
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  Fin (ForwardSortedFrontiers.frontiers c.T c.cut).length →
    List (BoundedNode b (k - (m + 1)))

/-- The full tuple of local D₂ marked points, in the inherited coordinate
order.  Both Γ₁ and Γ₂ coordinates participate in starred admissibility. -/
abbrev BulletTuple
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  MixedProduct.BulletIndex (kind c) → BoundedNode b (k - (m + 1))

/-- Membership in the selected roots together with the exact ordered
singleton-vector condition of the corrected starred Q domain. -/
def OrderedSupported
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (S : Supports c) (p : BulletTuple c) : Prop :=
  (∀ i, p i ∈ S i.1) ∧
  ∀ i j, i.1 < j.1 → (p i).1.length ≤ (p j).1.length

/-- Discard the Γ₁ entries only after the full ordered D₂ tuple has been
specified; the surviving colour has no marked-letter data. -/
def selectedPoints
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (p : BulletTuple c) :
    Corollary22ResidualPoints.PointTuple b (k - (m + 1)) gamma1 :=
  fun i => p i.1

/-- The pure support-selection obligation for a given residual colour.
It concerns ordered full-D₂ tuples and compares their Γ₂ restrictions. -/
def OrderedPointHomogeneous
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (S : Supports c)
    (residual : Corollary22ResidualPoints.PointTuple
      b (k - (m + 1)) gamma1 → γ) : Prop :=
  ∀ p p' : BulletTuple c,
    OrderedSupported c S p → OrderedSupported c S p' →
    residual (selectedPoints c gamma1 p) =
      residual (selectedPoints c gamma1 p')

private theorem source_kind_ne_up
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Fin (ForwardSortedFrontiers.frontiers c.T c.cut).length) :
    kind c i ≠ MixedProduct.CoordKind.up :=
  ForwardSortedMixedProduct.kind_ne_up c.source c.cut c.hcut c.hmax c.hout
    c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly i

/-- Every actual starred member of the smaller mixed span supplies an
ordered tuple in its specified support lists.  The order is proved from
starred membership and is not an additional caller premise. -/
theorem starred_points_ordered_supported
    {b n l k m q : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (g : Corollary22CanonicalQ.EnlargedWord c q)
    (fallback : α) (S : Supports c)
    (hsupport : ∀ i, (g.vector.components i).support = S i)
    (x : EnlargedStarredInput c fallback) (hx : x.1 ∈ g.span) :
    OrderedSupported c S x.1.bulletPoint := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [← hsupport i.1]
    exact hx.2.2 i
  · exact (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      c (eraseAux c fallback x.1)).1 x.2

/-- Ordered residual-point homogeneity makes the actual starred Q image
of a smaller mixed refinement monochromatic.  The original full-span
factorization supplies exact colours, even when its intermediate marker
moves leave the starred subset. -/
theorem Q_monochromatic_of_ordered_residual_homogeneous
    {b n l k m H q : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (f : Corollary22CanonicalQ.EnlargedWord c.core H)
    (g : Corollary22CanonicalQ.EnlargedWord c.core q)
    (fallback : α) (fallbackColor : γ)
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (total : EnlargedInput c.core → γ)
    (color : StarredObservation b n α → γ)
    (hH : 2 ≤ H) (hgood : MixedProduct.Good total f)
    (hsmooth : ∀ x y, MixedProduct.SmoothRelated gamma1 x y → total x = total y)
    (hagree : ∀ w : EnlargedStarredInput c.core fallback,
      total w.1 = color (starredObserve (fibreQStarredWord hb c fallback w)))
    (hgf : MixedProduct.VariableWord.Refines g f)
    (S : Supports c.core)
    (hsupport : ∀ i, (g.vector.components i).support = S i)
    (hmono : OrderedPointHomogeneous c.core gamma1 S
      (Corollary22ResidualPoints.residualColor f total gamma1 fallbackColor)) :
    ∀ x y : EnlargedStarredInput c.core fallback,
      x.1 ∈ g.span → y.1 ∈ g.span →
      color (starredObserve (fibreQStarredWord hb c fallback x)) =
        color (starredObserve (fibreQStarredWord hb c fallback y)) := by
  intro x y hx hy
  have hxcolor := Corollary22ResidualPoints.residualColor_exact_on_span
    f total gamma1 hH hgood hsmooth (Sum.inl fallback) fallbackColor x.1 (hgf hx)
  have hycolor := Corollary22ResidualPoints.residualColor_exact_on_span
    f total gamma1 hH hgood hsmooth (Sum.inl fallback) fallbackColor y.1 (hgf hy)
  have hsame := hmono x.1.bulletPoint y.1.bulletPoint
    (starred_points_ordered_supported c.core g fallback S hsupport x hx)
    (starred_points_ordered_supported c.core g fallback S hsupport y hy)
  exact (hagree x).symm.trans
    (hxcolor.symm.trans (hsame.trans (hycolor.trans (hagree y))))

/-- A complete local canonization assembly from the explicit geometric
selection input.  The total smooth Q colour is chosen BEFORE the original
c-good word.  Its residual colour is then fixed BEFORE the smaller support
family is selected.  A selected vector-complete family of height q≥2 with
ordered residual homogeneity constructs the genuine smaller good word and
an inhabited monochromatic canonical-signature fibre in the final word.

The two Ramsey existence steps are still inputs: the first good word and
the homogeneous full vector of support subsets.  Target coverage, target
inhabitation, syntactic refinements, root retention and the final colour
conclusion are proved here. -/
theorem exists_total_fibre_canonization_of_ordered_support_selection
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : StarredObservation b n α → γ)
    (hsimple : CanonicalTheoremSpec.SimpleWith B2 color) :
    let gamma1 := ForwardSemiCompleteSimplicity.gamma1OfBoundaryB2 hb c.core B2
    let sig := canonicalSignature hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    ∃ total : EnlargedInput c.core → γ,
      (∀ w : EnlargedStarredInput c.core fallback,
        total w.1 = color (starredObserve (fibreQStarredWord hb c fallback w))) ∧
      (∀ x y : EnlargedInput c.core,
        MixedProduct.SmoothRelated gamma1 x y → total x = total y) ∧
      ∀ (H : Nat) (f : Corollary22CanonicalQ.EnlargedWord c.core H),
        2 ≤ H → MixedProduct.Good total f →
        ∀ (q : Nat) (S : Supports c.core),
          (∀ i, (S i).Nodup) →
          (∀ i t, t ∈ S i → t ∈ (f.vector.components i).support) →
          VectorSkew.vectorCompleteB SkewTree.forwardAuxB q
            (fun i => (S i).map Subtype.val) = true →
          2 ≤ q →
          OrderedPointHomogeneous c.core gamma1 S
            (Corollary22ResidualPoints.residualColor f total gamma1 fallbackColor) →
          ∃ g : Corollary22CanonicalQ.EnlargedWord c.core q,
            (∀ i, (g.vector.components i).support = S i) ∧
            (∀ i, KVariableWord.SyntacticRefines
              (g.vector.components i) (f.vector.components i)) ∧
            MixedProduct.VariableWord.Refines g f ∧
            MixedProduct.Good total g ∧
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
              Lemma28.FibreMonochromatic sig
                (fun O => color (starredObserve O)) final (sig c.core.source) := by
  dsimp only
  have hsource := CanonicalTheoremSpec.sourceSimpleWithin_of_simpleWith
    c.ambient B2 color hsimple
  obtain ⟨total, hagree, hsmooth⟩ :=
    ForwardSemiCompleteSimplicity.exists_total_simpleWithin_Q_pullback
      hb c fallback fallbackColor B2 (fun O => color (starredObserve O)) hsource
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro H f hH hgood q S hnd hsub hvector hq hmono
  obtain ⟨g, hsupport, hsyntactic, hgf, hggood⟩ :=
    MixedSupportThinning.exists_good_thinning f (source_kind_ne_up c.core)
      S hnd hsub hvector (Sum.inl fallback) total hgood
  have hqpos : 0 < q := by omega
  refine ⟨g, hsupport, hsyntactic, hgf, hggood,
    enlargedInterpolatedFinalKWord c g fallback hb hqpos,
    enlargedFinal_syntacticallyRefines_ambient c g fallback,
    enlargedFinal_retains_initial_roots c g fallback,
    enlargedFinal_preserves_initial_symbols c g fallback,
    enlargedInterpolatedFinalKWord_span_nonempty c g fallback hb hqpos,
    Lemma27CanonicalWitness.canonicalSignature_fibre_nonempty hb
      (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
      c g fallback hqpos hq, ?_⟩
  exact fibreMonochromatic_of_Q_monochromatic hb
    (ForwardSemiCompleteCanonicalRoot.frame_l_pos hb c.core)
    c g fallback hqpos color
    (Q_monochromatic_of_ordered_residual_homogeneous hb c f g
      fallback fallbackColor
      (ForwardSemiCompleteSimplicity.gamma1OfBoundaryB2 hb c.core B2)
      total color hH hgood hsmooth hagree hgf S hsupport hmono)

end DualTree.Lemma27ResidualRefinement
