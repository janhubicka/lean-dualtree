import DualTree.ForwardSemiCompleteSimplicity
import DualTree.Corollary22TwoRootRepair

/-!
# Canonical boundary colour reduction for the actual corrected Q

Track E supplies a total globally smooth extension of the Q pullback
of a colouring simple in the source-independent corrected Definition 24.
The two-root repair can therefore be used on the FULL span of a genuine
c-good mixed word, although its marker moves need not remain starred.

The surviving data are exactly the canonical B2 boundary points of the
actual Q outputs. Equality of their projections reflects equality of the
local marked points, by injectivity of the genuine complete-support cone
map. There is no remaining agreement assumption on marked letters, on
Gamma1 points, or on whole coordinate words.

When B2 is empty, the Q image of the starred part of every such c-good
span is monochromatic. D2 coordinates may still be present: this is the
case where all of them belong to Gamma1, not an assumption that D2 is empty.

These theorems supply the colour reduction after the mixed word has been
constructed. They do not prove mixed Ramsey existence, CT refinement,
or a numerical MTHJ/CT bound. The c-goodness premise concerns the entire
enlarged-alphabet span, not only its starred subset.
-/

namespace DualTree.Corollary22CanonicalQ

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQEnlargedConstantWords
open ForwardSemiCompleteSimplicity

/-- The genuine enlarged-alphabet mixed words on a source frame's
safe common local domain. Intrinsic dimension is the separate parameter q. -/
abbrev EnlargedWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (q : Nat) :=
  MixedProduct.VariableWord b (k - (m + 1))
    (ForwardSortedFrontiers.frontiers c.T c.cut).length q
    (Sum α (Fin (m + 1))) (SkewTree.forwardAuxB (b := b)) (kind c)

/-- The canonical boundary point of an actual Q output retains exactly
its local marked point. The backward implication uses injectivity in one
fixed frontier cone, not merely separation of different frontier cones. -/
theorem canonicalPoint_Q_eq_iff_local_point_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : EnlargedStarredInput c.core fallback)
    (a : Boundary b l) :
    canonicalPoint (fibreQStarredWord hb c fallback x) a =
        canonicalPoint (fibreQStarredWord hb c fallback y) a ↔
      x.1.bulletPoint ((boundaryToD2 hb c.core) a) =
        y.1.bulletPoint ((boundaryToD2 hb c.core) a) := by
  rw [canonicalPoint_actual_Q hb c fallback x a,
    canonicalPoint_actual_Q hb c fallback y a]
  constructor
  · intro h
    have heq :
        markedProjection c.core (eraseAux c.core fallback x.1)
            ((boundaryToD2 hb c.core) a) =
          markedProjection c.core (eraseAux c.core fallback y.1)
            ((boundaryToD2 hb c.core) a) := Subtype.ext h
    exact ForwardInverseConeTails.projectCommon_injective
      c.core.T c.core.hcomplete c.core.hnon c.core.cut c.core.hcutT
      c.core.hm
      (ForwardOrderedProjections.frontierAt c.core.T c.core.cut
        ((boundaryToD2 hb c.core) a).1)
      (ForwardOrderedProjections.frontierAt_spec c.core.T c.core.cut
        ((boundaryToD2 hb c.core) a).1) heq
  · intro h
    simp only [markedProjection, eraseAux_bulletPoint, h]

/-- Equality on the selected canonical B2 boundary is exactly equality
of the Gamma2 local marked-point tuple, for actual corrected Q outputs. -/
theorem canonicalBoundary_eq_iff_gamma2_points
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (B2 : Set (Boundary b l))
    (x y : EnlargedStarredInput c.core fallback) :
    (∀ a : Boundary b l, a ∈ B2 →
      canonicalPoint (fibreQStarredWord hb c fallback x) a =
        canonicalPoint (fibreQStarredWord hb c fallback y) a) ↔
    (∀ i : MixedProduct.BulletIndex (kind c.core),
      gamma1OfBoundaryB2 hb c.core B2 i = false →
        x.1.bulletPoint i = y.1.bulletPoint i) := by
  constructor
  · intro h i hi
    obtain ⟨a, rfl⟩ := (boundaryToD2 hb c.core).surjective i
    exact (canonicalPoint_Q_eq_iff_local_point_eq hb c fallback x y a).1
      (h a ((gamma2_iff_boundaryB2 hb c.core B2 a).1 hi))
  · intro h a ha
    apply (canonicalPoint_Q_eq_iff_local_point_eq hb c fallback x y a).2
    exact h ((boundaryToD2 hb c.core) a)
      ((gamma2_iff_boundaryB2 hb c.core B2 a).2 ha)

/-- Corrected Definition 24 simplicity supplies a TOTAL globally smooth
Q extension. On every full-span c-good word of dimension at least two,
the colours of actual starred Q outputs depend only on their canonical
B2 boundary points. All marked-letter dependence has been eliminated.

The extension is chosen before the mixed word; c-goodness is a condition
on that actual extension and on the whole mixed span. -/
theorem exists_total_simple_Q_point_canonization
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (B2 : Set (Boundary b l))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : SimpleWithin c.ambient B2 color) :
    ∃ total : EnlargedInput c.core → γ,
      (∀ w : EnlargedStarredInput c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : EnlargedInput c.core,
        MixedProduct.SmoothRelated (gamma1OfBoundaryB2 hb c.core B2) x y →
          total x = total y) ∧
      (∀ (q : Nat) (f : EnlargedWord c.core q),
        2 ≤ q → MixedProduct.Good total f →
        ∀ x y : EnlargedStarredInput c.core fallback,
          x.1 ∈ f.span → y.1 ∈ f.span →
          (∀ a : Boundary b l, a ∈ B2 →
            canonicalPoint (fibreQStarredWord hb c fallback x) a =
              canonicalPoint (fibreQStarredWord hb c fallback y) a) →
          color (fibreQStarredWord hb c fallback x) =
            color (fibreQStarredWord hb c fallback y)) := by
  obtain ⟨total, hagree, hsmooth⟩ :=
    exists_total_simpleWithin_Q_pullback
      hb c fallback fallbackColor B2 color hsimple
  refine ⟨total, hagree, hsmooth, ?_⟩
  intro q f hq hgood x y hx hy hpoints
  have hlocal :=
    (canonicalBoundary_eq_iff_gamma2_points hb c fallback B2 x y).1 hpoints
  calc
    color (fibreQStarredWord hb c fallback x) = total x.1 := (hagree x).symm
    _ = total y.1 :=
      Corollary22TwoRootRepair.good_smooth_color_eq_of_two_le_dimension
        f total (gamma1OfBoundaryB2 hb c.core B2) hq hgood hsmooth
        (Sum.inl fallback) x.1 y.1 hx hy hlocal
    _ = color (fibreQStarredWord hb c fallback y) := hagree y

/-- In the empty-B2 case no CT selection of residual boundary points is
needed: every full-span c-good word of dimension at least two already
has monochromatic starred Q image. The existing D2 coordinates are all
Gamma1 coordinates, and need not form an empty index type. -/
theorem exists_total_emptyBoundary_Q_monochromatic
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : SimpleWithin c.ambient (∅ : Set (Boundary b l)) color) :
    ∃ total : EnlargedInput c.core → γ,
      (∀ w : EnlargedStarredInput c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : EnlargedInput c.core,
        MixedProduct.SmoothRelated (fun _ => true) x y → total x = total y) ∧
      (∀ (q : Nat) (f : EnlargedWord c.core q),
        2 ≤ q → MixedProduct.Good total f →
        ∀ x y : EnlargedStarredInput c.core fallback,
          x.1 ∈ f.span → y.1 ∈ f.span →
          color (fibreQStarredWord hb c fallback x) =
            color (fibreQStarredWord hb c fallback y)) := by
  obtain ⟨total, hagree, hsmooth, hfactor⟩ :=
    exists_total_simple_Q_point_canonization
      hb c fallback fallbackColor ∅ color hsimple
  have hgamma :
      gamma1OfBoundaryB2 hb c.core (∅ : Set (Boundary b l)) =
        (fun _ => true) := by
    funext i
    obtain ⟨a, rfl⟩ := (boundaryToD2 hb c.core).surjective i
    cases hg : gamma1OfBoundaryB2 hb c.core (∅ : Set (Boundary b l))
        ((boundaryToD2 hb c.core) a) with
    | false =>
        have ha := (gamma2_iff_boundaryB2 hb c.core ∅ a).1 hg
        cases ha
    | true => rfl
  refine ⟨total, hagree, ?_, ?_⟩
  · intro x y hxy
    exact hsmooth x y (by simpa only [hgamma] using hxy)
  · intro q f hq hgood x y hx hy
    exact hfactor q f hq hgood x y hx hy (by intro a ha; cases ha)

end DualTree.Corollary22CanonicalQ
