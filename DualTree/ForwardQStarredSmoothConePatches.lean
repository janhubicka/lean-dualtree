import DualTree.ForwardQActualStarredSpace
import DualTree.SmoothRelation
import DualTree.ConeLocalPatchSmoothness

/-!
# Actual corrected W-star points under smooth cone-local word patches

The corrected W-star D₀/D₂ domain is defined by the selected D₂
marked-point length vector, not by the letters of its coordinate
words. Consequently one may replace the letters of each bullet
word *inside its inclusive marked-point cone* without leaving
the corrected starred domain or changing the Q support.

The resulting mixed-product points are Gamma₂-smooth-related:
they have identical nonbullet-coordinate words and marked
points, and their bullet words coincide outside each marked
inclusive cone. Hence a colouring that is genuinely smooth
on the corrected starred domain takes the same value before
and after any such word patches.

This is a necessary colouring-pullback interface, but it
does NOT prove that the specific colouring induced by the
paper's Q construction is smooth. Nor does it identify the
local patched words with the particular mixed-cone word g_w.
-/

namespace DualTree.ForwardQStarredSmoothConePatches

open ForwardSourceQTree

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  Fin (ForwardSortedFrontiers.frontiers c.T c.cut).length

/-- Replace only bullet-coordinate word letters lying inside the
inclusive cone of that coordinate's unchanged marked point. -/
noncomputable def patchedInput
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    Input c := by
  classical
  exact {
    words := fun i =>
      if hi : kind c i = MixedProduct.CoordKind.bullet then
        MixedProduct.conePatch (x.bulletPoint ⟨i, hi⟩)
          (x.words i) (replacement i)
      else x.words i
    upPoint := x.upPoint
    bulletPoint := x.bulletPoint
  }

/-- Plain-coordinate and other nonbullet words stay literally
equal to the original words under a local cone patch. -/
theorem patchedInput_nonbullet
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α)
    (i : Index c)
    (hi : kind c i ≠ MixedProduct.CoordKind.bullet) :
    (patchedInput c x replacement).words i = x.words i := by
  classical
  simp [patchedInput, hi]

/-- Every bullet-coordinate patched word agrees with the original
word at positions outside the cone of its fixed marked point. -/
theorem patchedInput_bullet_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b (k - (m + 1)))
    (ht : ¬ IsPrefix (x.bulletPoint i).1 t.1) :
    (patchedInput c x replacement).words i.1 t =
      x.words i.1 t := by
  classical
  simp [patchedInput, i.2, MixedProduct.conePatch, ht]

/-- The corrected starred condition depends only on the D₂
marked-point array, so any such word patch preserves it. -/
theorem patchedInput_starred_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    ForwardQActualStarredSpace.IsStarred c
        (patchedInput c x replacement) ↔
      ForwardQActualStarredSpace.IsStarred c x := by
  rfl

/-- The Q-support tree depends on marked points and old source
interior, not on the words at any mixed-product coordinate. -/
theorem patchedInput_Q_nodes_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    nodes c (patchedInput c x replacement) = nodes c x := by
  rfl

/-- A patched input is again a real member of the corrected
starred W domain, not an unrestricted mixed-product element. -/
noncomputable def patchedStarred
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    ForwardQActualStarredSpace.StarredInput c :=
  ⟨patchedInput c x.1 replacement,
    (patchedInput_starred_iff c x.1 replacement).2 x.2⟩

/-- The old and patched actual starred mixed-product elements
are Gamma₂-smooth-related, by the literal Definition 21 relation. -/
theorem original_smooth_patched
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    MixedProduct.SmoothRelated (fun _ => false)
      x.1 (patchedStarred c x replacement).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change x.1.words i = (patchedInput c x.1 replacement).words i
    exact (patchedInput_nonbullet c x.1 replacement i hi).symm
  · intro i
    rfl
  · intro i
    change x.1.bulletPoint i =
        (patchedInput c x.1 replacement).bulletPoint i ∧
      ∀ t : BoundedNode b (k - (m + 1)),
        ¬ IsPrefix (x.1.bulletPoint i).1 t.1 →
          x.1.words i.1 t =
            (patchedInput c x.1 replacement).words i.1 t
    refine ⟨rfl, ?_⟩
    intro t ht
    exact (patchedInput_bullet_outside c x.1 replacement i t ht).symm

/-- Smoothness on the corrected starred subtype, without assuming
the colouring extends smoothly to the whole unstarred product. -/
def SmoothStarredColor
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) : Prop :=
  ∀ x y : ForwardQActualStarredSpace.StarredInput c,
    MixedProduct.SmoothRelated (fun _ => false) x.1 y.1 →
      color x = color y

/-- Any colouring satisfying the actual corrected starred
Gamma₂ smoothness condition is invariant under arbitrary
inside-cone patches that keep the selected marked points fixed. -/
theorem smooth_starred_color_invariant
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (hsmooth : SmoothStarredColor c color)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (replacement : Index c → TreeWord b (k - (m + 1)) α) :
    color x = color (patchedStarred c x replacement) :=
  hsmooth x (patchedStarred c x replacement)
    (original_smooth_patched c x replacement)

end DualTree.ForwardQStarredSmoothConePatches
