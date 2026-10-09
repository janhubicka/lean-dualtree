import DualTree.MixedElementFromMarkers
import DualTree.SmoothRelation
import DualTree.MixedGood

/-!
# Cone-local changes and the smoothness relation

Definition 21 allows a Gamma₂ bullet-coordinate word to vary *inside*
the inclusive successor cone of its marked point, while its marked
point and all letters outside that cone stay fixed.

This module constructs such changes, proves that arbitrary changes in
the marked cones are smooth-related, and checks a minimal counterexample:
the letter at the marked node need not be fixed by Gamma₂ smoothness.
Consequently an arbitrary colouring remembering that letter is not
automatically a smooth colouring. Any use of Corollary 22 for the
specific map Q in Lemma 27 must prove an additional compatibility
property; type-correct coordinate allocation alone is insufficient.
-/

namespace DualTree.MixedProduct

/-- Replace one word only inside the inclusive cone of a marked point. -/
noncomputable def conePatch
    {b n : Nat} {α : Type*}
    (root : BoundedNode b n)
    (base replacement : TreeWord b n α) :
    TreeWord b n α := by
  classical
  exact fun t =>
    if IsPrefix root.1 t.1 then replacement t else base t

/-- All letters outside a patched cone remain equal to the baseline. -/
theorem conePatch_outside
    {b n : Nat} {α : Type*}
    (root : BoundedNode b n)
    (base replacement : TreeWord b n α)
    (t : BoundedNode b n)
    (ht : ¬ IsPrefix root.1 t.1) :
    conePatch root base replacement t = base t := by
  classical
  simp [conePatch, ht]

/-- Inside the cone, the replacement word is used literally. -/
theorem conePatch_inside
    {b n : Nat} {α : Type*}
    (root : BoundedNode b n)
    (base replacement : TreeWord b n α)
    (t : BoundedNode b n)
    (ht : IsPrefix root.1 t.1) :
    conePatch root base replacement t = replacement t := by
  classical
  simp [conePatch, ht]

/-- Assign a baseline word at plain coordinates and a patched word
at every bullet coordinate, using its uniquely selected marker. -/
noncomputable def patchedWords
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (i : Fin d) : TreeWord b n α := by
  classical
  exact if hi : bulletKindOfRange index i = .bullet then
    conePatch (point (markerOfBullet index ⟨i, hi⟩))
      (base i) (replacement i)
  else base i

/-- The plain coordinates are never modified. -/
theorem patchedWords_plain
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (i : Fin d)
    (hi : bulletKindOfRange index i = .plain) :
    patchedWords index base replacement point i = base i := by
  classical
  simp [patchedWords, hi]

/-- At a bullet coordinate, the patched word agrees with the
baseline outside the cone of its corresponding marker point. -/
theorem patchedWords_bullet_outside
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (i : BulletIndex (bulletKindOfRange index))
    (t : BoundedNode b n)
    (ht : ¬ IsPrefix (point (markerOfBullet index i)).1 t.1) :
    patchedWords index base replacement point i.1 t = base i.1 t := by
  classical
  simp [patchedWords, i.2, conePatch, ht]

/-- The marked coordinate uses its replacement word at every point
inside its selected inclusive cone. -/
theorem patchedWords_bullet_inside
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n)
    (i : BulletIndex (bulletKindOfRange index))
    (t : BoundedNode b n)
    (ht : IsPrefix (point (markerOfBullet index i)).1 t.1) :
    patchedWords index base replacement point i.1 t =
      replacement i.1 t := by
  classical
  simp [patchedWords, i.2, conePatch, ht]

/-- A concrete mixed-product element with freely modified word
coordinates only inside the marked bullet cones. -/
noncomputable def patchedElement
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n) :
    Element b n d α (bulletKindOfRange index) :=
  elementFromMarkers index
    (patchedWords index base replacement point) point

/--
All locally modified mixed elements with the same background words
and marked points are Gamma₂-smooth-related. Their letters *inside*
the selected cones may be completely different.
-/
theorem patchedElement_smooth
    {b n d : Nat} {α M : Type*}
    (index : M → Fin d)
    (base replacement₁ replacement₂ : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n) :
    SmoothRelated (fun _ => false)
      (patchedElement index base replacement₁ point)
      (patchedElement index base replacement₂ point) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hplain : bulletKindOfRange index i = .plain := by
      cases hkind : bulletKindOfRange index i with
      | bullet => exact False.elim (hi hkind)
      | up => exact False.elim (bulletKindOfRange_ne_up index i hkind)
      | plain => rfl
    change patchedWords index base replacement₁ point i =
      patchedWords index base replacement₂ point i
    rw [patchedWords_plain index base replacement₁ point i hplain,
      patchedWords_plain index base replacement₂ point i hplain]
  · intro i
    exact False.elim (bulletKindOfRange_ne_up index i.1 i.2)
  · intro i
    change
      (patchedElement index base replacement₁ point).bulletPoint i =
        (patchedElement index base replacement₂ point).bulletPoint i ∧
      (∀ t : BoundedNode b n,
        ¬ IsPrefix
            ((patchedElement index base replacement₁ point).bulletPoint i).1 t.1 →
          (patchedElement index base replacement₁ point).words i.1 t =
            (patchedElement index base replacement₂ point).words i.1 t)
    refine ⟨rfl, ?_⟩
    intro t ht
    change
      ¬ IsPrefix (point (markerOfBullet index i)).1 t.1 at ht
    change patchedWords index base replacement₁ point i.1 t =
      patchedWords index base replacement₂ point i.1 t
    exact (patchedWords_bullet_outside index base replacement₁ point i t ht).trans
      (patchedWords_bullet_outside index base replacement₂ point i t ht).symm

/-- Any colouring genuinely constant on Gamma₂ smoothness classes
is insensitive to arbitrary changes inside the marked cones. -/
theorem smoothColor_invariant_under_patches
    {b n d : Nat} {α γ M : Type*}
    (index : M → Fin d)
    (color : Element b n d α (bulletKindOfRange index) → γ)
    (hsmooth : ∀ x y,
      SmoothRelated (fun _ => false) x y → color x = color y)
    (base replacement₁ replacement₂ : Fin d → TreeWord b n α)
    (point : M → BoundedNode b n) :
    color (patchedElement index base replacement₁ point) =
      color (patchedElement index base replacement₂ point) :=
  hsmooth _ _ (patchedElement_smooth index base replacement₁ replacement₂ point)

end DualTree.MixedProduct

namespace DualTree.BulletSmoothnessAudit

/-- One bullet coordinate in a two-level binary homogeneous tree. -/
def onlyBullet : Fin 1 → MixedProduct.CoordKind := fun _ => .bullet

/-- The empty ambient root is a valid bounded marked point. -/
def root : BoundedNode 2 2 :=
  ⟨[], by simp [InHomTree]⟩

/-- The two constant Boolean words. -/
def zeroWord : TreeWord 2 2 Bool := fun _ => false
def oneWord : TreeWord 2 2 Bool := fun _ => true

/-- A mixed element whose marked point carries the letter false. -/
def zeroElement : MixedProduct.Element 2 2 1 Bool onlyBullet where
  words := fun _ => zeroWord
  upPoint := fun i => by
    cases i with
    | mk j hj => cases hj
  bulletPoint := fun _ => root

/-- A mixed element differing only in the letter at the marked point. -/
def oneElement : MixedProduct.Element 2 2 1 Bool onlyBullet where
  words := fun _ => oneWord
  upPoint := fun i => by
    cases i with
    | mk j hj => cases hj
  bulletPoint := fun _ => root

/-- These elements are Gamma₂-smooth-related because the marked
point is the root and hence has no exterior positions. -/
theorem related_despite_different_marked_letters :
    MixedProduct.SmoothRelated (fun _ => false)
      zeroElement oneElement := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact False.elim (h rfl)
  · intro i
    cases i with
    | mk j hj => cases hj
  · intro i
    change
      zeroElement.bulletPoint i = oneElement.bulletPoint i ∧
      (∀ t : BoundedNode 2 2,
        ¬ IsPrefix (zeroElement.bulletPoint i).1 t.1 →
          zeroElement.words i.1 t = oneElement.words i.1 t)
    refine ⟨rfl, ?_⟩
    intro t ht
    have hp : IsPrefix (zeroElement.bulletPoint i).1 t.1 :=
      ⟨t.1, by simp [zeroElement, root]⟩
    exact False.elim (ht hp)

/-- The letter at the single designated bullet point. -/
def markedLetterColor (x : MixedProduct.Element 2 2 1 Bool onlyBullet) : Bool :=
  x.words (0 : Fin 1) (x.bulletPoint ⟨0, rfl⟩)

/-- The most natural marked-letter colouring is not smooth even
in this smallest model: Gamma₂ permits the marked letter to change. -/
theorem markedLetterColor_not_smooth :
    ¬ ∀ x y : MixedProduct.Element 2 2 1 Bool onlyBullet,
      MixedProduct.SmoothRelated (fun _ => false) x y →
        markedLetterColor x = markedLetterColor y := by
  intro h
  have heq := h zeroElement oneElement
    related_despite_different_marked_letters
  simp [markedLetterColor, zeroElement, oneElement,
    zeroWord, oneWord] at heq

end DualTree.BulletSmoothnessAudit
