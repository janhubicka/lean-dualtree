import DualTree.MixedRefinement

/-!
# c-goodness with no bullet coordinates

Definition 11 retains only the D2/bullet data.  Therefore when D2 is empty,
c-goodness is exactly monochromaticity of the generated mixed span.

This elementary equivalence is the logical base case used when reducing
Theorem 13 to the D2=0 Ramsey statement.
-/

namespace DualTree.MixedProduct

/-- The coordinate partition has no D2/bullet coordinate. -/
def NoBullet {d : Nat} (kind : Fin d → CoordKind) : Prop :=
  ∀ i, kind i ≠ CoordKind.bullet

theorem noBulletIndex_elim {d : Nat}
    {kind : Fin d → CoordKind}
    (h : NoBullet kind)
    (i : BulletIndex kind) : False :=
  h i.1 i.2

/--
If D2 is empty, Definition 11's c-goodness is exactly constancy on the whole
mixed span.
-/
theorem good_iff_constant_on_span_of_noBullet
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (hnb : NoBullet kind)
    (c : Element b n d α kind → γ)
    (f : VariableWord b n d k α aux kind) :
    Good c f ↔
      ∀ ⦃x y : Element b n d α kind⦄,
        x ∈ f.span → y ∈ f.span → c x = c y := by
  constructor
  · intro hgood x y hx hy
    apply hgood hx hy
    · intro i
      exact False.elim (noBulletIndex_elim hnb i)
    · intro i
      exact False.elim (noBulletIndex_elim hnb i)
  · intro hmono x y hx hy _ _
    exact hmono hx hy

/-- A monochromatic further subspace is c-good in the D2=empty case. -/
theorem good_of_constant_on_span_of_noBullet
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (hnb : NoBullet kind)
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    (hmono : ∀ ⦃x y : Element b n d α kind⦄,
      x ∈ f.span → y ∈ f.span → c x = c y) :
    Good c f :=
  (good_iff_constant_on_span_of_noBullet hnb c f).2 hmono

end DualTree.MixedProduct
