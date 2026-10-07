import DualTree.GoodNoBullet

/-!
# The canonical invariant of Lemma 14

Lemma 14 treats the D2=empty mixed product.  It produces a subspace on which
the color is determined by, for each D1/up coordinate:
* the selected top-level node x_i; and
* the values of the word along the predecessor chain of x_i.

This file isolates that source-facing invariant before formalizing the
Hales--Jewett construction that produces it.
-/

namespace DualTree.MixedProduct

/--
The data compared in Lemma 14: identical D1 leaf points and identical word
values on all predecessors of those leaf points.
-/
def SameUpTrace
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (x y : Element b n d α kind) : Prop :=
  (∀ i : UpIndex kind, x.upPoint i = y.upPoint i) ∧
  (∀ i : UpIndex kind, ∀ t : BoundedNode b n,
    IsPrefix t.1 (x.upPoint i).1 →
      x.words i.1 t = y.words i.1 t)

/--
The conclusion of Lemma 14 on a generated mixed subspace.
-/
def UpCanonical
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (c : Element b n d α kind → γ)
    (f : VariableWord b n d k α aux kind) : Prop :=
  ∀ ⦃x y : Element b n d α kind⦄,
    x ∈ f.span →
    y ∈ f.span →
    SameUpTrace x y →
    c x = c y

theorem sameUpTrace_refl
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (x : Element b n d α kind) :
    SameUpTrace x x := by
  constructor
  · intro i
    rfl
  · intro i t _
    rfl

/-- The Lemma 14 invariant is inherited by every further mixed subspace. -/
theorem upCanonical_of_refines
    {b n d k k' : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    {g : VariableWord b n d k' α aux kind}
    (hcanon : UpCanonical c f)
    (hgf : VariableWord.Refines g f) :
    UpCanonical c g := by
  intro x y hx hy htrace
  exact hcanon (hgf hx) (hgf hy) htrace

/--
In the D2=empty case, a c-good subspace is automatically Lemma-14 canonical;
indeed c-goodness is then full monochromaticity.
-/
theorem upCanonical_of_good_of_noBullet
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (hnb : NoBullet kind)
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    (hgood : Good c f) :
    UpCanonical c f := by
  have hmono :=
    (good_iff_constant_on_span_of_noBullet hnb c f).1 hgood
  intro x y hx hy _
  exact hmono hx hy

/-- Full monochromaticity is stronger than the Lemma 14 invariant. -/
theorem upCanonical_of_constant_on_span
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    (hmono : ∀ ⦃x y : Element b n d α kind⦄,
      x ∈ f.span → y ∈ f.span → c x = c y) :
    UpCanonical c f := by
  intro x y hx hy _
  exact hmono hx hy

end DualTree.MixedProduct
