import DualTree.MixedGoodSmoothRecordFactorization

/-!
# A TOTAL colour on reduced D₂/Γ₁ records

Finite Ramsey theorems normally colour all points of a type, rather
than a partially-defined domain. The preceding module constructed
the exact Option-valued colour of every realized reduced bullet
record, without assuming a nonempty colour type.

When a fallback colour is supplied (as it always can be for a
nonempty finite colour set), fill the unrealized records with that
colour. This yields a genuine total map from the reduced record type
to the original colour type γ, and exactly reproduces the original
colour on every element of a smooth c-good mixed word's span.

The proof requires NO additional Ramsey theorem, and does not
assert that any residual record becomes constant. It provides an
explicit total finite-colour interface for the later iteration.
-/

namespace DualTree.MixedProduct

/-- Extend the genuine partial colour on realized Γ₁ records
to an everywhere-defined γ-colouring, with the specified
fallback colour used only outside the realized record set. -/
noncomputable def totalColorOnReducedRecords
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (fallbackColor : γ) :
    (BulletIndex kind → (BoundedNode b n × Option β)) → γ :=
  fun r => (colorOnReducedRecords f c gamma1 r).getD fallbackColor

/-- Given Definition-11 c-goodness and Definition-21
smoothness, the ACTUAL colour of every genuine span element is
the total record colour evaluated at its reduced record.
Nothing asserts equality of the records themselves. -/
theorem totalColorOnReducedRecords_exact_on_span
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y,
      SmoothRelated gamma1 x y → c x = c y)
    (fallback : β)
    (fallbackColor : γ)
    (x : Element b n d β kind)
    (hx : x ∈ f.span) :
    totalColorOnReducedRecords f c gamma1 fallbackColor
        (reducedBulletRecord gamma1 x) = c x := by
  simp [totalColorOnReducedRecords,
    colorOnReducedRecords_exact_on_span
      f c gamma1 hgood hsmooth fallback x hx]

end DualTree.MixedProduct
