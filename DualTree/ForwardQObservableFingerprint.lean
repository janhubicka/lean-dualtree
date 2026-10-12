import DualTree.ForwardQProjectedSmoothObservables
import DualTree.ForwardQStarredSmoothPartitions

/-!
# Canonical observable fingerprint for an arbitrary Gamma1/Gamma2 split

This finite-coordinate fingerprint is a COMPLETE invariant of the
Definition 21 SmoothRelated equivalence relation on the ACTUAL
forward-corrected D0/D2 mixed-product space.

Its word record is unchanged on D0 and Gamma1; on Gamma2 it
replaces exactly the inclusive marked cone with a fixed fallback
letter and retains the word outside that cone. Its point record
keeps Gamma2 marked points but deliberately ignores Gamma1 points.

Equality of these two concrete finite records is equivalent to
SmoothRelated, including the case of moving Gamma1 marked points.
Consequently a colouring of the actual corrected W-star subtype
is smooth for a chosen partition precisely when it factors through
the observable fingerprint. The factor map is total: choose a
starred representative for fingerprints in the image and use the
specified fallback colour outside the image.

This eliminates all arbitrary pointwise comparisons from the
abstract smoothness criterion. It does NOT prove that the
particular Definition 24 simple colouring, pulled back along
the paper's three-way Q word, factors through this record.
The canonical A/B1/B2-to-R/Gamma correspondence and variable
span/induction remain separate mathematical obligations.
-/

namespace DualTree.ForwardQObservableFingerprint

open ForwardSourceQTree

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Keep a whole word on plain/Gamma1 coordinates. At a Gamma2
coordinate mask the inclusive marked cone with a fixed letter. -/
noncomputable def maskedLetter
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) : α := by
  classical
  exact if hi : kind c i = MixedProduct.CoordKind.bullet then
    if gamma1 ⟨i, hi⟩ then
      x.words i z
    else
      if IsPrefix (x.bulletPoint ⟨i, hi⟩).1 z.1 then
        fallback
      else
        x.words i z
  else
    x.words i z

/-- Only Gamma2 marked points can affect the smoothness class.
At Gamma1 the selected marked point is entirely unobserved. -/
def observedPoint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c)) :
    Option (BoundedNode b (k - (m + 1))) :=
  if gamma1 j then none else some (x.bulletPoint j)

/-- An explicit, typed finite observable record, with no
dependent equality between different Q output supports. -/
abbrev Fingerprint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  (Index c → TreeWord b (k - (m + 1)) α) ×
    (MixedProduct.BulletIndex (kind c) →
      Option (BoundedNode b (k - (m + 1))))

noncomputable def fingerprint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c) : Fingerprint c :=
  ⟨fun i z => maskedLetter c gamma1 fallback x i z,
    observedPoint c gamma1 x⟩

/-- At every D0 coordinate the mask is literally the input letter. -/
theorem maskedLetter_nonbullet
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c)
    (i : Index c)
    (hi : kind c i ≠ MixedProduct.CoordKind.bullet)
    (z : BoundedNode b (k - (m + 1))) :
    maskedLetter c gamma1 fallback x i z = x.words i z := by
  classical
  simp [maskedLetter, hi]

/-- At Gamma1 the complete local word survives masking. -/
theorem maskedLetter_gamma1
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c))
    (hg : gamma1 j = true)
    (z : BoundedNode b (k - (m + 1))) :
    maskedLetter c gamma1 fallback x j.1 z =
      x.words j.1 z := by
  classical
  simp [maskedLetter, j.2, hg]

/-- Outside a Gamma2 marked cone, masking preserves the actual
input coordinate letter. -/
theorem maskedLetter_gamma2_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c))
    (hg : gamma1 j = false)
    (z : BoundedNode b (k - (m + 1)))
    (hout : ¬ IsPrefix (x.bulletPoint j).1 z.1) :
    maskedLetter c gamma1 fallback x j.1 z =
      x.words j.1 z := by
  classical
  simp [maskedLetter, j.2, hg, hout]

/-- Inside a Gamma2 marked cone, the record stores the
fallback letter, not an arbitrary word symbol. -/
theorem maskedLetter_gamma2_inside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c))
    (hg : gamma1 j = false)
    (z : BoundedNode b (k - (m + 1)))
    (hin : IsPrefix (x.bulletPoint j).1 z.1) :
    maskedLetter c gamma1 fallback x j.1 z =
      fallback := by
  classical
  simp [maskedLetter, j.2, hg, hin]

/-- Smooth comparison fixes the masked letter array, including
the masked Gamma2 cones and the entire Gamma1 words. -/
theorem maskedLetter_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    maskedLetter c gamma1 fallback x i z =
      maskedLetter c gamma1 fallback y i z := by
  classical
  by_cases hi : kind c i = MixedProduct.CoordKind.bullet
  · let j : MixedProduct.BulletIndex (kind c) := ⟨i, hi⟩
    cases hg : gamma1 j with
    | true =>
        have hw : x.words i z = y.words i z := by
          have hwords : x.words j.1 = y.words j.1 := by
            simpa [hg] using hxy.2.2 j
          exact congrFun hwords z
        simpa [maskedLetter, hi, j, hg] using hw
    | false =>
        have hp :
            x.bulletPoint j = y.bulletPoint j ∧
              ∀ t : BoundedNode b (k - (m + 1)),
                ¬ IsPrefix (x.bulletPoint j).1 t.1 →
                  x.words j.1 t = y.words j.1 t := by
          simpa [hg] using hxy.2.2 j
        by_cases hz : IsPrefix (x.bulletPoint j).1 z.1
        · have hy : IsPrefix (y.bulletPoint j).1 z.1 := by
            simpa [← hp.1] using hz
          have hxm :=
            maskedLetter_gamma2_inside c gamma1 fallback x j hg z hz
          have hym :=
            maskedLetter_gamma2_inside c gamma1 fallback y j hg z hy
          exact hxm.trans hym.symm
        · have hy : ¬ IsPrefix (y.bulletPoint j).1 z.1 := by
            simpa [← hp.1] using hz
          have hxm :=
            maskedLetter_gamma2_outside c gamma1 fallback x j hg z hz
          have hym :=
            maskedLetter_gamma2_outside c gamma1 fallback y j hg z hy
          calc
            maskedLetter c gamma1 fallback x i z = x.words i z := hxm
            _ = y.words i z := hp.2 z hz
            _ = maskedLetter c gamma1 fallback y i z := hym.symm
  · have hw : x.words i z = y.words i z :=
      congrFun (hxy.1 i hi) z
    simpa [maskedLetter, hi] using hw

/-- Smooth-related points have identical Gamma2 point records.
Gamma1 selected points are intentionally invisible. -/
theorem observedPoint_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y)
    (j : MixedProduct.BulletIndex (kind c)) :
    observedPoint c gamma1 x j = observedPoint c gamma1 y j := by
  cases hg : gamma1 j with
  | true => simp [observedPoint, hg]
  | false =>
      have hp :
          x.bulletPoint j = y.bulletPoint j ∧
            ∀ t : BoundedNode b (k - (m + 1)),
              ¬ IsPrefix (x.bulletPoint j).1 t.1 →
                x.words j.1 t = y.words j.1 t := by
        simpa [hg] using hxy.2.2 j
      simp [observedPoint, hg, hp.1]

/-- Smooth-related inputs have exactly the same fingerprint. -/
theorem fingerprint_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y) :
    fingerprint c gamma1 fallback x =
      fingerprint c gamma1 fallback y := by
  apply Prod.ext
  · funext i z
    exact maskedLetter_eq_of_smooth c gamma1 fallback x y hxy i z
  · funext j
    exact observedPoint_eq_of_smooth c gamma1 x y hxy j

/-- Conversely the two fingerprint records recover the ENTIRE
Definition 21 comparison, with no need to fix Gamma1 marked points. -/
theorem smooth_of_fingerprint_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x y : Input c)
    (h : fingerprint c gamma1 fallback x =
      fingerprint c gamma1 fallback y) :
    MixedProduct.SmoothRelated gamma1 x y := by
  have hwords :
      (fun i z => maskedLetter c gamma1 fallback x i z) =
      (fun i z => maskedLetter c gamma1 fallback y i z) :=
    congrArg Prod.fst h
  have hpoints :
      observedPoint c gamma1 x =
      observedPoint c gamma1 y :=
    congrArg Prod.snd h
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    funext z
    have heq := congrFun (congrFun hwords i) z
    simpa [maskedLetter, hi] using heq
  · intro i
    have hno : kind c i.1 ≠ MixedProduct.CoordKind.up :=
      ForwardSortedMixedProduct.kind_ne_up
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly i.1
    exact False.elim (hno i.2)
  · intro j
    cases hg : gamma1 j with
    | true =>
        have heq : x.words j.1 = y.words j.1 := by
          funext z
          have hw := congrFun (congrFun hwords j.1) z
          simpa [maskedLetter, j.2, hg] using hw
        simpa [hg] using heq
    | false =>
        have hm : observedPoint c gamma1 x j =
            observedPoint c gamma1 y j :=
          congrFun hpoints j
        have hp : x.bulletPoint j = y.bulletPoint j := by
          have hs : some (x.bulletPoint j) =
              some (y.bulletPoint j) := by
            simpa [observedPoint, hg] using hm
          exact Option.some.inj hs
        have hout :
            ∀ z : BoundedNode b (k - (m + 1)),
              ¬ IsPrefix (x.bulletPoint j).1 z.1 →
                x.words j.1 z = y.words j.1 z := by
          intro z hz
          have hy : ¬ IsPrefix (y.bulletPoint j).1 z.1 := by
            simpa [← hp] using hz
          have hxm :=
            maskedLetter_gamma2_outside c gamma1 fallback x j hg z hz
          have hym :=
            maskedLetter_gamma2_outside c gamma1 fallback y j hg z hy
          calc
            x.words j.1 z = maskedLetter c gamma1 fallback x j.1 z :=
              hxm.symm
            _ = maskedLetter c gamma1 fallback y j.1 z :=
              congrFun (congrFun hwords j.1) z
            _ = y.words j.1 z := hym
        simpa [hg] using And.intro hp hout

/-- The exact complete observable normal form of arbitrary
Gamma1/Gamma2 smoothness on the ACTUAL corrected mixed product. -/
theorem fingerprint_eq_iff_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (x y : Input c) :
    fingerprint c gamma1 fallback x =
      fingerprint c gamma1 fallback y ↔
      MixedProduct.SmoothRelated gamma1 x y :=
  ⟨smooth_of_fingerprint_eq c gamma1 fallback x y,
    fingerprint_eq_of_smooth c gamma1 fallback x y⟩

/-- Smooth colourings of the corrected W-star space are EXACTLY
those factoring through its observable fingerprint. The factor
map extends to all fingerprints, even ones not realized by any
genuine starred mixed-product input. -/
theorem smoothStarred_iff_factors_through_fingerprint
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallbackLetter : α)
    (fallbackColor : γ)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) :
    ForwardQStarredSmoothPartitions.SmoothStarredFor c gamma1 color ↔
      ∃ f : Fingerprint c → γ,
        ∀ x : ForwardQActualStarredSpace.StarredInput c,
          color x = f (fingerprint c gamma1 fallbackLetter x.1) := by
  constructor
  · intro hsmooth
    classical
    let f : Fingerprint c → γ := fun record =>
      if h : ∃ x : ForwardQActualStarredSpace.StarredInput c,
          fingerprint c gamma1 fallbackLetter x.1 = record then
        color (Classical.choose h)
      else fallbackColor
    refine ⟨f, ?_⟩
    intro x
    have hx : ∃ y : ForwardQActualStarredSpace.StarredInput c,
        fingerprint c gamma1 fallbackLetter y.1 =
          fingerprint c gamma1 fallbackLetter x.1 := ⟨x, rfl⟩
    have hchoice :
        fingerprint c gamma1 fallbackLetter (Classical.choose hx).1 =
          fingerprint c gamma1 fallbackLetter x.1 :=
      Classical.choose_spec hx
    have hrel :
        MixedProduct.SmoothRelated gamma1 (Classical.choose hx).1 x.1 :=
      (fingerprint_eq_iff_smooth c gamma1 fallbackLetter
        (Classical.choose hx).1 x.1).1 hchoice
    have hcol : color (Classical.choose hx) = color x :=
      hsmooth (Classical.choose hx) x hrel
    dsimp [f]
    simp only [dif_pos hx]
    exact hcol.symm
  · rintro ⟨f, hfactor⟩ x y hxy
    calc
      color x = f (fingerprint c gamma1 fallbackLetter x.1) := hfactor x
      _ = f (fingerprint c gamma1 fallbackLetter y.1) :=
        congrArg f (fingerprint_eq_of_smooth
          c gamma1 fallbackLetter x.1 y.1 hxy)
      _ = color y := (hfactor y).symm

end DualTree.ForwardQObservableFingerprint
