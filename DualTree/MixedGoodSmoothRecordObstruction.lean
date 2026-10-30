import DualTree.MixedGoodSmoothReducedRecord
import DualTree.MixedGoodStarredSpanObstruction

/-!
# Γ₁ residual-record variation obstructs full starred-span constancy

The smooth/c-good reduction retains every D₂ marked point and, at Γ₁
indices, the observed letter at that point. This is the *correct*
finite residual invariant for Definition 11 plus Definition 21.

The genuine local component variable rooted at a selected D₂ point
can be reassigned to two different enlarged letters. Both evaluations
stay in the original mixed-variable-word span, and the corrected
starred predicate depends only on marked points. Thus for any
positive-dimensional genuine enlarged Lemma-27 mixed word, and every
Γ₁ marked index, its reduced record is NONCONSTANT on the full
corrected starred mixed span.

This is a structural obstruction, even before any colouring is
chosen. In particular a corrected finite Ramsey theorem cannot
require constancy of this entire residual record whenever Γ₁ is
nonempty. One must instead work with record-dependent colours
and the actual later induction.

The observed-letter colouring used below is c-good, but is NOT
claimed smooth for arbitrary Γ₁/Γ₂ partitions. The independently
verified height-one SMOOTH counterexample remains in
Corollary22Audit. None of the results below claims a counterexample
to the full dual-tree Ramsey theorem.
-/

namespace DualTree.MixedProduct

/-- The exact coordinatewise record which remains after removing
the irrelevant Γ₂ observed letters using Definition-21 smoothness.
Unlike full bulletRecord, only Γ₁ observed letters are present. -/
def reducedBulletRecord
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (x : Element b n d β kind) :
    BulletIndex kind → (BoundedNode b n × Option β) :=
  fun i =>
    (x.bulletPoint i,
      if gamma1 i then some (x.words i.1 (x.bulletPoint i))
      else none)

/-- Equality of the reduced bullet records is equivalent to
equality of ALL marked D₂ points plus agreement of observed
letters precisely at the Γ₁ subset. -/
theorem reducedBulletRecord_eq_iff
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (x y : Element b n d β kind) :
    reducedBulletRecord gamma1 x = reducedBulletRecord gamma1 y ↔
    (∀ i : BulletIndex kind, x.bulletPoint i = y.bulletPoint i) ∧
    (∀ i : BulletIndex kind, gamma1 i = true →
      x.words i.1 (x.bulletPoint i) =
        y.words i.1 (y.bulletPoint i)) := by
  constructor
  · intro hrec
    constructor
    · intro i
      exact congrArg Prod.fst (congrFun hrec i)
    · intro i hi
      have h := congrArg Prod.snd (congrFun hrec i)
      change
        (if gamma1 i then
          some (x.words i.1 (x.bulletPoint i)) else none) =
        (if gamma1 i then
          some (y.words i.1 (y.bulletPoint i)) else none) at h
      simpa only [hi, ite_true, Option.some.injEq] using h
  · rintro ⟨hpoint, hletter⟩
    funext i
    apply Prod.ext
    · exact hpoint i
    · cases hi : gamma1 i with
      | false => simp [reducedBulletRecord, hi]
      | true =>
        change
          (if gamma1 i then
            some (x.words i.1 (x.bulletPoint i)) else none) =
          (if gamma1 i then
            some (y.words i.1 (y.bulletPoint i)) else none)
        simpa only [hi, ite_true, Option.some.injEq]
          using hletter i hi

/-- Source-facing color factorization on the genuine span through
the *reduced* Γ₁/D₂ record. This uses the verified simultaneous
Γ₂ normalization, not any stronger starred monochromaticity. -/
theorem good_smooth_color_eq_of_reducedBulletRecord
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
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hrec : reducedBulletRecord gamma1 x =
      reducedBulletRecord gamma1 y) :
    c x = c y := by
  rcases (reducedBulletRecord_eq_iff gamma1 x y).1 hrec with
    ⟨hpoints, hletters⟩
  exact good_smooth_color_eq_of_reduced_bullet_record
    f c gamma1 hgood hsmooth fallback x y hx hy hpoints hletters

end DualTree.MixedProduct

namespace DualTree.MixedGoodSmoothRecordObstruction

open MixedProduct
open MixedGoodStarredSpanObstruction
open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- A purely local, alphabet-generic structural obstruction:
any actual marked root at a Γ₁ index can be evaluated with two
distinct letters, producing TWO legal points of the very same
mixed span whose Γ₁ reduced bullet records differ. This does
not require a distinguished starred predicate. -/
theorem exists_distinct_reduced_records_in_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (gamma1 : BulletIndex kind → Bool)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (hgamma : gamma1 i = true)
    (a b' : β) (hab : a ≠ b') :
    ∃ y z : Element b n d β kind,
      y ∈ f.span ∧ z ∈ f.span ∧
      reducedBulletRecord gamma1 y ≠
        reducedBulletRecord gamma1 z := by
  let y := recolorBullet f x i a
  let z := recolorBullet f x i b'
  refine ⟨y, z,
    recolorBullet_mem_span f x hx i a,
    recolorBullet_mem_span f x hx i b', ?_⟩
  intro hrec
  have hi := congrArg Prod.snd (congrFun hrec i)
  have hletters : some a = some b' := by
    change
      (if gamma1 i then
        some (colorAtBullet i y) else none) =
      (if gamma1 i then
        some (colorAtBullet i z) else none) at hi
    simpa only [hgamma, ite_true,
      colorAtBullet_recolor f x hx i a,
      colorAtBullet_recolor f x hx i b'] using hi
  exact hab (Option.some.inj hletters)

/-- No genuine positive-dimensional enlarged local mixed word can
make the residual Γ₁ record constant on its corrected STARRED span
if Γ₁ contains a real D₂ marker. The enlarged alphabet always has
at least two distinct letters (original vs auxiliary), even if the
original alphabet itself is a singleton.

This uses the already kernel-checked actual starred-point existence
and the obstruction to monochromaticity of the marked-letter
colouring. No assertion of smoothness for that colouring is made. -/
theorem no_constant_reduced_record_on_enlarged_starred_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hq : 0 < q)
    (gamma1 : BulletIndex (kind g.core) → Bool)
    (i : BulletIndex (kind g.core))
    (hgamma : gamma1 i = true) :
    ¬ (∀ y z : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      y.1 ∈ f.span → z.1 ∈ f.span →
      reducedBulletRecord gamma1 y.1 =
        reducedBulletRecord gamma1 z.1) := by
  intro hconst
  apply no_full_starred_monochromaticity_from_good
    g f fallback hq i
  intro y z hy hz
  have hrec := hconst y z hy hz
  have hletter := congrArg Prod.snd (congrFun hrec i)
  change
    (if gamma1 i then some (colorAtBullet i y.1) else none) =
    (if gamma1 i then some (colorAtBullet i z.1) else none)
      at hletter
  simpa only [hgamma, ite_true, Option.some.injEq] using hletter

/-- This obstruction holds *alongside* the genuine c-good
property of the observed-letter colouring: the flaw in a proposed
full-record-constancy theorem is not failure to obtain c-goodness.
No general smoothness assertion is made for the selected colouring. -/
theorem good_color_with_nonconstant_reduced_record
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hq : 0 < q)
    (gamma1 : BulletIndex (kind g.core) → Bool)
    (i : BulletIndex (kind g.core))
    (hgamma : gamma1 i = true) :
    Good (colorAtBullet i) f ∧
      ¬ (∀ y z : ForwardQEnlargedConstantWords.EnlargedStarredInput
          g.core fallback,
        y.1 ∈ f.span → z.1 ∈ f.span →
        reducedBulletRecord gamma1 y.1 =
          reducedBulletRecord gamma1 z.1) :=
  ⟨colorAtBullet_good f i,
    no_constant_reduced_record_on_enlarged_starred_span
      g f fallback hq gamma1 i hgamma⟩

end DualTree.MixedGoodSmoothRecordObstruction
