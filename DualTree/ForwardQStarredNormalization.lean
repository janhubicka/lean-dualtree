import DualTree.ForwardQStarredPatchCriterion

/-!
# Canonical representatives of Gamma₂ smoothness classes on corrected W-star

Fix one alphabet letter a. Normalize a corrected starred mixed input
by replacing every bullet word INSIDE its inclusive marked cone with
the constant letter a, leaving the entire outside word record,
nonbullet words and all marked points untouched.

We prove that normalization is idempotent and that two actual
corrected starred inputs are Gamma₂-smooth-related if and only if
they have exactly the same normalized representative. Thus every
colouring after normalization is automatically smooth.

This suggests a possible repair mechanism for the colouring
pullback in Lemma 27, but it is NOT a completed repair: the paper
also requires specific local decoding and the full image/span of Q.
Normalizing first might destroy those properties. Surjectivity,
homogeneity and compatibility with the particular construction
must be checked separately.
-/

namespace DualTree.ForwardQStarredNormalization

open ForwardSourceQTree
open ForwardQStarredSmoothConePatches
open ForwardQStarredPatchCriterion

/-- Equality of elements with the same three literal fields.
This avoids dependent elimination on a word array occurring
inside the patch expression itself. -/
private theorem input_ext
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (p q : Input c)
    (hwords : p.words = q.words)
    (hup : p.upPoint = q.upPoint)
    (hbullet : p.bulletPoint = q.bulletPoint) :
    p = q := by
  cases p with
  | mk wp up bp =>
    cases q with
    | mk wq uq bq =>
      cases hwords
      cases hup
      cases hbullet
      rfl

/-- A second cone patch completely overrides the first patch
inside every bullet cone, while outside the cones neither patch
changes the original input. The marked points are fixed. -/
theorem patchedInput_override
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (r₁ r₂ : Index c → TreeWord b (k - (m + 1)) α) :
    patchedInput c (patchedInput c x r₁) r₂ =
      patchedInput c x r₂ := by
  classical
  have hw :
      (patchedInput c (patchedInput c x r₁) r₂).words =
        (patchedInput c x r₂).words := by
    funext i t
    by_cases hi : kind c i = MixedProduct.CoordKind.bullet
    · by_cases ht : IsPrefix (x.bulletPoint ⟨i, hi⟩).1 t.1
      · simp [patchedInput, hi, MixedProduct.conePatch, ht]
      · simp [patchedInput, hi, MixedProduct.conePatch, ht]
    · simp [patchedInput, hi]
  exact input_ext c _ _ hw rfl rfl

/-- A canonical W-star representative using one fixed alphabet letter
inside every inclusive marked cone. This keeps all marked points,
selected D₂ order and the corrected Q support unchanged. -/
noncomputable def normalizeStarred
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (letter : α)
    (x : ForwardQActualStarredSpace.StarredInput c) :
    ForwardQActualStarredSpace.StarredInput c :=
  patchedStarred c x (fun _ _ => letter)

/-- Smooth-related corrected starred inputs have identical
canonical representatives: first reconstruct y as a patch
of x, then use the patch override theorem. -/
theorem normalizeStarred_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (letter : α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (hxy : MixedProduct.SmoothRelated (fun _ => false) x.1 y.1) :
    normalizeStarred c letter x = normalizeStarred c letter y := by
  apply Subtype.ext
  change patchedInput c x.1 (fun _ _ => letter) =
    patchedInput c y.1 (fun _ _ => letter)
  calc
    patchedInput c x.1 (fun _ _ => letter) =
        patchedInput c
          (patchedInput c x.1 (fun i => y.1.words i))
          (fun _ _ => letter) :=
      (patchedInput_override c x.1 (fun i => y.1.words i)
        (fun _ _ => letter)).symm
    _ = patchedInput c y.1 (fun _ _ => letter) := by
      rw [reconstruct_mixed_input_from_smooth c x.1 y.1 hxy]

/-- Complete normal form for Gamma₂ smoothness on the
corrected starred subtype: two inputs are equivalent
if and only if their canonical masked mixed words are equal. -/
theorem smoothRelated_iff_normalizeStarred_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (letter : α)
    (x y : ForwardQActualStarredSpace.StarredInput c) :
    MixedProduct.SmoothRelated (fun _ => false) x.1 y.1 ↔
      normalizeStarred c letter x = normalizeStarred c letter y := by
  constructor
  · exact normalizeStarred_eq_of_smooth c letter x y
  · intro hn
    have hx := original_smooth_patched c x (fun _ _ => letter)
    have hy := original_smooth_patched c y (fun _ _ => letter)
    change MixedProduct.SmoothRelated (fun _ => false)
      x.1 (normalizeStarred c letter x).1 at hx
    change MixedProduct.SmoothRelated (fun _ => false)
      y.1 (normalizeStarred c letter y).1 at hy
    have hv :
        (normalizeStarred c letter x).1 =
          (normalizeStarred c letter y).1 :=
      congrArg Subtype.val hn
    rw [hv] at hx
    exact MixedProduct.smoothRelated_trans (fun _ => false)
      hx (MixedProduct.smoothRelated_symm (fun _ => false) hy)

/-- Normalizing an already normalized starred input has no
further effect (the representative is idempotent). -/
theorem normalizeStarred_idempotent
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (letter : α)
    (x : ForwardQActualStarredSpace.StarredInput c) :
    normalizeStarred c letter (normalizeStarred c letter x) =
      normalizeStarred c letter x := by
  apply Subtype.ext
  change
    patchedInput c
      (patchedInput c x.1 (fun _ _ => letter))
      (fun _ _ => letter) =
    patchedInput c x.1 (fun _ _ => letter)
  exact patchedInput_override c x.1
    (fun _ _ => letter) (fun _ _ => letter)

/-- The composition of ANY output map with the canonical
normalization and an arbitrary colouring is automatically
Gamma₂-smooth on the ACTUAL corrected starred source.
This does not assert that normalized Q has the range or
the mixed-cone semantics required by Lemma 27. -/
theorem normalized_pullback_is_smooth
    {b n l k m : Nat} {α β γ : Type*}
    (c : Frame b n l k m α)
    (letter : α)
    (Q : ForwardQActualStarredSpace.StarredInput c → β)
    (color : β → γ) :
    SmoothStarredColor c
      (fun x => color (Q (normalizeStarred c letter x))) := by
  intro x y hxy
  exact congrArg
    (fun z : ForwardQActualStarredSpace.StarredInput c => color (Q z))
    (normalizeStarred_eq_of_smooth c letter x y hxy)

end DualTree.ForwardQStarredNormalization
