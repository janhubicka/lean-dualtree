import DualTree.MixedGoodSmoothRecordObstruction

/-!
# Actual colours on the reduced Γ₁/D₂ record space

A corrected mixed Ramsey argument cannot force the complete reduced
Γ₁ record to be constant (proved in the preceding module), but it
may canonize the *colour relative to that record*.

Given a colouring c of a genuine mixed-product span, this module
constructs an actual partially-defined colour function on the reduced
record type. We use Option γ for undefined/unrealized records, avoiding
any artificial assumption that the colour type γ is inhabited.
The choice of a representative is immaterial whenever c is c-good
and smooth: the preceding proven Γ₂ normalization ensures equal
reduced records imply equal colours on the genuine span.

This is a concrete finite-record factorization interface for a
future mixed Ramsey induction, not an existence theorem for a
c-good word or a claim that residual records are constant.
-/

namespace DualTree.MixedProduct

/-- An actual partial colouring of reduced Γ₁/D₂ records.
It assigns some (c x) to a realized record using one chosen
point x of the TRUE mixed span, and none to unrealized records.
No Nonempty γ assumption is required. -/
noncomputable def colorOnReducedRecords
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool) :
    (BulletIndex kind → (BoundedNode b n × Option β)) → Option γ :=
  by
    classical
    exact fun record =>
      if h : ∃ x : Element b n d β kind,
          x ∈ f.span ∧ reducedBulletRecord gamma1 x = record then
        some (c (Classical.choose h))
      else
        none

/-- Every record occurring in the actual mixed span receives
exactly the original colour, provided c is c-good on f and
globally Γ₁/Γ₂ smooth. Thus the factor does not depend on the
arbitrary representative chosen from that record fibre. -/
theorem colorOnReducedRecords_exact_on_span
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β)
    (x : Element b n d β kind) (hx : x ∈ f.span) :
    colorOnReducedRecords f c gamma1 (reducedBulletRecord gamma1 x) =
      some (c x) := by
  classical
  have hex : ∃ y : Element b n d β kind,
      y ∈ f.span ∧ reducedBulletRecord gamma1 y =
        reducedBulletRecord gamma1 x :=
    ⟨x, hx, rfl⟩
  have hy := Classical.choose_spec hex
  have hcol : c (Classical.choose hex) = c x :=
    good_smooth_color_eq_of_reducedBulletRecord
      f c gamma1 hgood hsmooth fallback
      (Classical.choose hex) x hy.1 hx hy.2
  unfold colorOnReducedRecords
  simp only [dif_pos hex]
  exact congrArg Option.some hcol

/-- The partial colour is undefined exactly on records that
are not attained by any actual point of the generated span. -/
theorem colorOnReducedRecords_eq_none_iff
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (record : BulletIndex kind →
      (BoundedNode b n × Option β)) :
    colorOnReducedRecords f c gamma1 record = none ↔
      ¬ ∃ x : Element b n d β kind,
        x ∈ f.span ∧ reducedBulletRecord gamma1 x = record := by
  classical
  unfold colorOnReducedRecords
  by_cases h : ∃ x : Element b n d β kind,
      x ∈ f.span ∧ reducedBulletRecord gamma1 x = record
  · simp [h]
  · simp [h]

/-- A factorization on all realized reduced records is UNIQUE
there: any other partial colouring which agrees with c on the
actual span has the same value as the constructed canonical
record colouring. No assertion is made on unrealized records. -/
theorem colorOnReducedRecords_unique_on_realized
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β)
    (other : (BulletIndex kind →
      (BoundedNode b n × Option β)) → Option γ)
    (hother : ∀ x : Element b n d β kind,
      x ∈ f.span →
        other (reducedBulletRecord gamma1 x) = some (c x))
    (record : BulletIndex kind → (BoundedNode b n × Option β))
    (hreal : ∃ x : Element b n d β kind,
      x ∈ f.span ∧ reducedBulletRecord gamma1 x = record) :
    other record = colorOnReducedRecords f c gamma1 record := by
  obtain ⟨x,hx,hr⟩ := hreal
  rw [← hr, hother x hx,
    colorOnReducedRecords_exact_on_span
      f c gamma1 hgood hsmooth fallback x hx]

/-- Conversely, if *any* partial record colouring exactly
represents c throughout the genuine span, then c is already
constant on every reduced-record fibre (regardless of
smoothness assumptions). This is the exact logical criterion
for a corrected colour canonization statement. -/
theorem color_eq_of_factor_through_reducedBulletRecord
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (factor : (BulletIndex kind →
      (BoundedNode b n × Option β)) → Option γ)
    (hfactor : ∀ x : Element b n d β kind,
      x ∈ f.span →
        factor (reducedBulletRecord gamma1 x) = some (c x))
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hrecord : reducedBulletRecord gamma1 x =
      reducedBulletRecord gamma1 y) :
    c x = c y := by
  have ha := hfactor x hx
  have hb := hfactor y hy
  rw [hrecord, hb] at ha
  exact Option.some.inj ha.symm

end DualTree.MixedProduct
