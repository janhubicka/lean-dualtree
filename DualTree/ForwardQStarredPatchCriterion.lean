import DualTree.ForwardQStarredSmoothConePatches

/-!
# Smoothness equals invariance under every marked-cone patch

Definition 21's Gamma₂ relation has a *converse* to the existing
cone-patch lemma: for two actual corrected starred inputs, if they
are smooth-related, patching the first input with the second input's
coordinate words reproduces the second input exactly.

Thus arbitrary local cone patches generate the full smoothness
equivalence relation on the corrected W-star subtype. The induced
colouring c ∘ Q is smooth exactly when its colours are invariant
under these patches. An arbitrary target map Q is smooth for every
post-colouring only when Q itself is patch-invariant.

This is an exact reduction of the Lemma 27 colouring obligation.
It does not assert that the paper's particular Q satisfies the
criterion. The starred-input order and local height assumptions
remain the same as in ForwardQActualStarredSpace.
-/

namespace DualTree.ForwardQStarredPatchCriterion

open ForwardSourceQTree
open ForwardQStarredSmoothConePatches

/-- Every Gamma₂-smooth-related mixed input is *literally*
obtained from the first by replacing its bullet words inside
their selected marked cones with the second input's words. -/
theorem reconstruct_mixed_input_from_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (fun _ => false) x y) :
    patchedInput c x (fun i => y.words i) = y := by
  classical
  have hwords :
      (patchedInput c x (fun i => y.words i)).words = y.words := by
    funext i t
    by_cases hi : kind c i = MixedProduct.CoordKind.bullet
    · by_cases ht : IsPrefix (x.bulletPoint ⟨i, hi⟩).1 t.1
      · simp [patchedInput, hi, MixedProduct.conePatch, ht]
      · have hcoord :
            x.bulletPoint ⟨i, hi⟩ = y.bulletPoint ⟨i, hi⟩ ∧
            ∀ u : BoundedNode b (k - (m + 1)),
              ¬ IsPrefix (x.bulletPoint ⟨i, hi⟩).1 u.1 →
                x.words i u = y.words i u := by
          simpa using hxy.2.2 ⟨i, hi⟩
        have houtside := hcoord.2 t ht
        simpa [patchedInput, hi, MixedProduct.conePatch, ht] using houtside
    · have hplain := hxy.1 i hi
      simpa [patchedInput, hi] using congrFun hplain t
  have hup :
      (patchedInput c x (fun i => y.words i)).upPoint = y.upPoint := by
    change x.upPoint = y.upPoint
    funext i
    exact hxy.2.1 i
  have hbullet :
      (patchedInput c x (fun i => y.words i)).bulletPoint =
        y.bulletPoint := by
    change x.bulletPoint = y.bulletPoint
    funext i
    have hi :
        x.bulletPoint i = y.bulletPoint i ∧
          ∀ t : BoundedNode b (k - (m + 1)),
            ¬ IsPrefix (x.bulletPoint i).1 t.1 →
              x.words i.1 t = y.words i.1 t := by
      simpa using hxy.2.2 i
    exact hi.1
  cases hx : patchedInput c x (fun i => y.words i) with
  | mk wx ux bx =>
    cases hy : y with
    | mk wy uy by_ =>
      simp only [hx, hy] at hwords hup hbullet ⊢
      cases hwords
      cases hup
      cases hbullet
      rfl

/-- On the ACTUAL corrected W-star subtype, two points are
smooth-related if and only if one is the patch of the other
by its full coordinate-word array. In particular this is
not merely a sufficient condition for smoothness. -/
theorem smoothRelated_iff_patchedStarred_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c) :
    MixedProduct.SmoothRelated (fun _ => false) x.1 y.1 ↔
      patchedStarred c x (fun i => y.1.words i) = y := by
  constructor
  · intro hxy
    apply Subtype.ext
    change patchedInput c x.1 (fun i => y.1.words i) = y.1
    exact reconstruct_mixed_input_from_smooth c x.1 y.1 hxy
  · intro hpatch
    have hrel := original_smooth_patched c x (fun i => y.1.words i)
    simpa only [hpatch] using hrel

/-- For a colouring of the genuine corrected starred input
subtype, invariance under ALL marked-cone word replacements
is necessary as well as sufficient for Gamma₂-smoothness. -/
theorem smoothStarred_iff_all_patches
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ) :
    SmoothStarredColor c color ↔
      ∀ (x : ForwardQActualStarredSpace.StarredInput c)
        (replacement : Index c → TreeWord b (k - (m + 1)) α),
          color x = color (patchedStarred c x replacement) := by
  constructor
  · intro hsmooth x replacement
    exact smooth_starred_color_invariant c color hsmooth x replacement
  · intro hinvariant x y hxy
    have hpatch :
        patchedStarred c x (fun i => y.1.words i) = y :=
      (smoothRelated_iff_patchedStarred_eq c x y).1 hxy
    calc
      color x =
          color (patchedStarred c x (fun i => y.1.words i)) :=
        hinvariant x (fun i => y.1.words i)
      _ = color y := congrArg color hpatch

/-- A map Q on actual starred inputs yields a smooth pullback
under every endocolouring of its output if and only if Q is
itself invariant under all marked-cone patches. Applying the
forward implication to the identity colouring shows that
this strong hypothesis cannot be silently inferred for an
arbitrary word-construction map Q. -/
theorem all_endocolors_smooth_iff_Q_patch_invariant
    {b n l k m : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (Q : ForwardQActualStarredSpace.StarredInput c → β) :
    (∀ color : β → β,
      SmoothStarredColor c (fun x => color (Q x))) ↔
      (∀ (x : ForwardQActualStarredSpace.StarredInput c)
        (replacement : Index c → TreeWord b (k - (m + 1)) α),
          Q x = Q (patchedStarred c x replacement)) := by
  constructor
  · intro htotal
    have hidentity : SmoothStarredColor c Q := by
      simpa using htotal (fun z : β => z)
    exact (smoothStarred_iff_all_patches c Q).1 hidentity
  · intro hQ color
    apply (smoothStarred_iff_all_patches c (fun x => color (Q x))).2
    intro x replacement
    exact congrArg color (hQ x replacement)

end DualTree.ForwardQStarredPatchCriterion
