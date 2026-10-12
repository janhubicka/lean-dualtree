import DualTree.ForwardQStarredSmoothExtension

/-!
# Arbitrary Gamma1/Gamma2 splits in Definition 21

The published notion of a smooth colouring existentially chooses a
partition D2 = Gamma1 ⊔ Gamma2. A Gamma1 word is fixed in its entirety
but its marked point can move. At Gamma2, the marked point and the
outside-cone letters are fixed, while cone letters can vary.

Our earlier corrected-starred smoothness results considered only
Gamma1 = ∅. This module provides the genuinely existential API and
a binary witness that this special case is strictly stronger.
It remains to transport Definition 24's B1/B2 simplicity witness
through the particular Q construction in Lemma 27.
-/

namespace DualTree.ForwardQStarredSmoothPartitions

open ForwardSourceQTree

def SmoothStarredFor
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) : Prop :=
  ∀ x y : ForwardQActualStarredSpace.StarredInput c,
    MixedProduct.SmoothRelated gamma1 x.1 y.1 →
      color x = color y

def HasSmoothPartition
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) : Prop :=
  ∃ gamma1 : MixedProduct.BulletIndex (kind c) → Bool,
    SmoothStarredFor c gamma1 color

/-- For each partition, the partial starred colouring extends to
a total smooth colouring exactly when it is compatible on the
smooth-related pairs inside the corrected starred subtype. -/
theorem smooth_starred_extension_iff
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (fallback : γ) :
    (∃ total : Input c → γ,
      (∀ x : ForwardQActualStarredSpace.StarredInput c,
        total x.1 = color x) ∧
      (∀ x y : Input c,
        MixedProduct.SmoothRelated gamma1 x y →
          total x = total y)) ↔
      SmoothStarredFor c gamma1 color := by
  constructor
  · rintro ⟨total, hagree, htotal⟩ x y hxy
    calc
      color x = total x.1 := (hagree x).symm
      _ = total y.1 := htotal x.1 y.1 hxy
      _ = color y := hagree y
  · intro hsmooth
    let D : Set (Input c) :=
      {x | ForwardQActualStarredSpace.IsStarred c x}
    have hcompatible :
        ∀ (x y : Input c) (hx : x ∈ D) (hy : y ∈ D),
          MixedProduct.SmoothRelated gamma1 x y →
            (fun z : {z : Input c // z ∈ D} =>
              color ⟨z.1, z.2⟩) ⟨x, hx⟩ =
            (fun z : {z : Input c // z ∈ D} =>
              color ⟨z.1, z.2⟩) ⟨y, hy⟩ := by
      intro x y hx hy hxy
      exact hsmooth ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨total, hmatch, htotal⟩ :=
      MixedProduct.exists_smooth_extension gamma1
        D (fun z : {z : Input c // z ∈ D} =>
          color ⟨z.1, z.2⟩) fallback hcompatible
    refine ⟨total, ?_, htotal⟩
    intro x
    simpa [D] using hmatch x.1 x.2

/-- Exact extension criterion for SOME partition, rather
than the earlier special case Gamma1 empty. -/
theorem exists_partition_total_extension_iff
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (fallback : γ) :
    (∃ gamma1 : MixedProduct.BulletIndex (kind c) → Bool,
      ∃ total : Input c → γ,
        (∀ x : ForwardQActualStarredSpace.StarredInput c,
          total x.1 = color x) ∧
        (∀ x y : Input c,
          MixedProduct.SmoothRelated gamma1 x y →
            total x = total y)) ↔
      HasSmoothPartition c color := by
  constructor
  · rintro ⟨gamma1, total, hagree, hsmooth⟩
    exact ⟨gamma1,
      (smooth_starred_extension_iff c gamma1 color fallback).1
        ⟨total, hagree, hsmooth⟩⟩
  · rintro ⟨gamma1, hclass⟩
    obtain ⟨total, hagree, hsmooth⟩ :=
      (smooth_starred_extension_iff c gamma1 color fallback).2 hclass
    exact ⟨gamma1, total, hagree, hsmooth⟩

/-- For Gamma1 = D2 every coordinate word is fixed.
Thus every colouring of the whole word array is smooth. -/
theorem whole_word_coloring_is_smooth
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (f : (ForwardQStarredSmoothConePatches.Index c →
      TreeWord b (k - (m + 1)) α) → γ) :
    SmoothStarredFor c (fun _ => true) (fun x => f x.1.words) := by
  intro x y hxy
  have hw : x.1.words = y.1.words := by
    funext i
    by_cases hi : kind c i = MixedProduct.CoordKind.bullet
    · simpa using hxy.2.2 ⟨i, hi⟩
    · exact hxy.1 i hi
  exact congrArg f hw

theorem whole_word_coloring_has_smooth_partition
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (f : (ForwardQStarredSmoothConePatches.Index c →
      TreeWord b (k - (m + 1)) α) → γ) :
    HasSmoothPartition c (fun x => f x.1.words) :=
  ⟨fun _ => true, whole_word_coloring_is_smooth c f⟩

theorem gamma2_all_has_smooth_partition
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (hall : ForwardQStarredSmoothConePatches.SmoothStarredColor c color) :
    HasSmoothPartition c color :=
  ⟨fun _ => false, hall⟩

namespace StrictnessWitness

/-- A colouring of the letter at a FIXED ambient root, not
at the varying marked-point location. -/
def rootLetterColor
    (x : MixedProduct.Element 2 2 1 Bool
      BulletSmoothnessAudit.onlyBullet) : Bool :=
  x.words (0 : Fin 1) BulletSmoothnessAudit.root

theorem rootLetterColor_gamma1_all :
    ∀ x y : MixedProduct.Element 2 2 1 Bool
        BulletSmoothnessAudit.onlyBullet,
      MixedProduct.SmoothRelated (fun _ => true) x y →
        rootLetterColor x = rootLetterColor y := by
  intro x y hxy
  have hw : x.words (0 : Fin 1) = y.words (0 : Fin 1) := by
    simpa using hxy.2.2 ⟨0, rfl⟩
  exact congrFun hw BulletSmoothnessAudit.root

theorem rootLetterColor_not_gamma2_all :
    ¬ ∀ x y : MixedProduct.Element 2 2 1 Bool
        BulletSmoothnessAudit.onlyBullet,
      MixedProduct.SmoothRelated (fun _ => false) x y →
        rootLetterColor x = rootLetterColor y := by
  intro h
  have hdiff := h BulletSmoothnessAudit.zeroElement
      BulletSmoothnessAudit.oneElement
      BulletSmoothnessAudit.related_despite_different_marked_letters
  simp [rootLetterColor, BulletSmoothnessAudit.zeroElement,
    BulletSmoothnessAudit.oneElement,
    BulletSmoothnessAudit.zeroWord, BulletSmoothnessAudit.oneWord] at hdiff

theorem smooth_for_some_partition_but_not_gamma2_all :
    (∃ gamma1 : MixedProduct.BulletIndex
        BulletSmoothnessAudit.onlyBullet → Bool,
      ∀ x y : MixedProduct.Element 2 2 1 Bool
        BulletSmoothnessAudit.onlyBullet,
        MixedProduct.SmoothRelated gamma1 x y →
          rootLetterColor x = rootLetterColor y) ∧
    (¬ ∀ x y : MixedProduct.Element 2 2 1 Bool
        BulletSmoothnessAudit.onlyBullet,
      MixedProduct.SmoothRelated (fun _ => false) x y →
        rootLetterColor x = rootLetterColor y) :=
  ⟨⟨fun _ => true, rootLetterColor_gamma1_all⟩,
    rootLetterColor_not_gamma2_all⟩

end StrictnessWitness

end DualTree.ForwardQStarredSmoothPartitions
