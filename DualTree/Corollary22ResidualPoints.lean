import DualTree.Corollary22TwoRootRepair
import DualTree.MixedRefinement

/-!
# A total colour on the surviving local Γ₂ points

For a genuine c-good mixed word of intrinsic dimension at least two,
global smoothness makes the colour depend only on the Γ₂ marked points.
The two-root argument has already removed all marked-letter dependence
and all Γ₁ point dependence on the whole mixed span.

This module makes the remaining colour an actual total function.  It
chooses a representative only from the supplied word's genuine span,
and uses a fallback colour on tuples with no such representative.
Exactness holds at every span element.  Homogenizing this residual colour
on the tuples realized in a further mixed refinement makes that entire
smaller mixed span monochromatic.

The residual colour is chosen AFTER the original mixed word.  In the Q
application, the original total smooth colour must still be chosen BEFORE
that c-good word.  Neither support selection, a Ramsey refinement, nor a
numerical bound is constructed here.  D₁ coordinates are allowed in this
algebraic factorization; their data have already been erased by Good.
-/

namespace DualTree.Corollary22ResidualPoints

open MixedProduct

/-- The bullet coordinates whose marked points survive smoothness. -/
abbrev PointIndex
    {d : Nat} {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool) :=
  {i : BulletIndex kind // gamma1 i = false}

/-- One actual local bounded node at each surviving Γ₂ coordinate. -/
abbrev PointTuple
    (b n : Nat) {d : Nat} {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool) :=
  PointIndex gamma1 → BoundedNode b n

/-- The Γ₂ marked-point tuple of a genuine mixed-product element. -/
def pointTuple
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (x : Element b n d β kind) : PointTuple b n gamma1 :=
  fun i => x.bulletPoint i.1

/-- Only tuples realized by elements of this actual mixed span matter
for the subsequent residual-colour homogenization. -/
def realizedTuples
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (gamma1 : BulletIndex kind → Bool) : Set (PointTuple b n gamma1) :=
  {p | ∃ x : Element b n d β kind,
    x ∈ f.span ∧ pointTuple gamma1 x = p}

/-- A total residual colour, defined after the mixed word `f` is fixed.
The representative is required to belong to the full genuine span of
`f`; the fallback is used precisely outside its realized Γ₂ tuples. -/
noncomputable def residualColor
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (fallbackColor : γ) (p : PointTuple b n gamma1) : γ := by
  classical
  exact if h : ∃ x : Element b n d β kind,
      x ∈ f.span ∧ pointTuple gamma1 x = p then
    c (Classical.choose h)
  else fallbackColor

/-- Full-span c-goodness and global smoothness make the total residual
colour exact at every genuine span element.  No marked letters or Γ₁
points occur in its argument. -/
theorem residualColor_exact_on_span
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hk : 2 ≤ k)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β) (fallbackColor : γ)
    (x : Element b n d β kind) (hx : x ∈ f.span) :
    residualColor f c gamma1 fallbackColor (pointTuple gamma1 x) = c x := by
  classical
  have h : ∃ y : Element b n d β kind,
      y ∈ f.span ∧ pointTuple gamma1 y = pointTuple gamma1 x :=
    ⟨x, hx, rfl⟩
  simp only [residualColor, dite_eq_left h]
  apply Corollary22TwoRootRepair.good_smooth_color_eq_of_two_le_dimension
    f c gamma1 hk hgood hsmooth fallback (Classical.choose h) x
    (Classical.choose_spec h).1 hx
  intro i hi
  exact congrFun (Classical.choose_spec h).2 (⟨i, hi⟩ : PointIndex gamma1)

/-- The original colour factors through an actual total function of the
Γ₂ points on the whole mixed span.  The supplied word is not manufactured
by this factorization, and no homogeneity of the residual colour is claimed. -/
theorem exists_total_point_factor
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hk : 2 ≤ k)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β) (fallbackColor : γ) :
    ∃ residual : PointTuple b n gamma1 → γ,
      ∀ x : Element b n d β kind, x ∈ f.span →
        residual (pointTuple gamma1 x) = c x := by
  exact ⟨residualColor f c gamma1 fallbackColor,
    residualColor_exact_on_span
      f c gamma1 hk hgood hsmooth fallback fallbackColor⟩

/-- If the residual colour of `f` is homogeneous on the point tuples
realized in a genuine mixed refinement `g`, the whole span of `g` is
monochromatic for the original colour.  The points themselves may vary.
The dimension-at-least-two resource is needed in `f`, where the residual
colour was made exact; this transfer imposes no new dimension condition. -/
theorem monochromatic_of_residualColor_homogeneous
    {b n d k k' : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (g : MixedProduct.VariableWord b n d k' β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hk : 2 ≤ k)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β) (fallbackColor : γ)
    (hgf : MixedProduct.VariableWord.Refines g f)
    (hmono : ∀ p q : PointTuple b n gamma1,
      p ∈ realizedTuples g gamma1 → q ∈ realizedTuples g gamma1 →
      residualColor f c gamma1 fallbackColor p =
        residualColor f c gamma1 fallbackColor q) :
    ∀ x y : Element b n d β kind,
      x ∈ g.span → y ∈ g.span → c x = c y := by
  intro x y hx hy
  have hxcolor := residualColor_exact_on_span
    f c gamma1 hk hgood hsmooth fallback fallbackColor x (hgf hx)
  have hycolor := residualColor_exact_on_span
    f c gamma1 hk hgood hsmooth fallback fallbackColor y (hgf hy)
  have hsame := hmono (pointTuple gamma1 x) (pointTuple gamma1 y)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  exact hxcolor.symm.trans (hsame.trans hycolor)

end DualTree.Corollary22ResidualPoints
