import DualTree.ForwardQStarredNormalization

/-!
# Loss of information under canonical smoothness normalization

The corrected Gamma₂ smoothness classes admit canonical constant-letter
representatives.  That operation makes any subsequent colouring smooth,
but cannot be treated as a surjective change of coordinates on the
starred mixed-product input domain.

At every actual D₂ coordinate, the normalized input has the chosen
letter at its fixed marked point.  Replacing that entire local cone
by a different letter gives another *actual corrected starred input*,
still with the same Q support, which is absent from the image of
normalization.  This proves nonsurjectivity whenever Wstar is
inhabited, D₂ is nonempty and the alphabet has two letters.

The obstruction does not refute a Ramsey theorem: that theorem may
require only a carefully selected monochromatic span, not a surjective
map onto every starred input.  It does show that smoothness
normalization alone is insufficient to recover the full Lemma 27
local word family and its required span/refinement properties.
-/

namespace DualTree.ForwardQNormalizationObstruction

open ForwardSourceQTree
open ForwardQStarredSmoothConePatches
open ForwardQStarredNormalization

/-- The actual letter carried by a selected D₂ coordinate
at its own marked (bounded) node. -/
def markedLetter
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c) : α :=
  x.1.words i.1 (x.1.bulletPoint i)

/-- A cone patched to a constant letter has that letter
at the marked node.  This is an inclusive, not strict,
cone: the marked point itself is overwritten. -/
theorem markedLetter_patched_constant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c)
    (letter : α) :
    markedLetter c i (patchedStarred c x (fun _ _ => letter)) =
      letter := by
  classical
  change
    (patchedInput c x.1 (fun _ _ => letter)).words i.1
      (x.1.bulletPoint i) = letter
  simp [patchedInput, i.2, MixedProduct.conePatch, isPrefix_refl]

/-- All normalized corrected starred inputs have the same
specified letter at each of their own marked D₂ points. -/
theorem markedLetter_normalized
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c)
    (letter : α) :
    markedLetter c i (normalizeStarred c letter x) = letter :=
  markedLetter_patched_constant c i x letter

/-- Normalizing the mixed-product words leaves the literal
Q support unchanged.  The loss of information demonstrated
below is a word/image issue, not a geometric-Q failure. -/
theorem normalized_Q_nodes_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (letter : α) :
    nodes c (normalizeStarred c letter x).1 =
      nodes c x.1 :=
  patchedInput_Q_nodes_eq c x.1 (fun _ _ => letter)

/-- The starred input patched to a different constant at a
selected marked cone is not in the image of normalization.
Both inputs have exactly the same marked points and Q support. -/
theorem patched_other_letter_not_in_normalization_range
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c)
    (a other : α)
    (hne : a ≠ other) :
    ∀ z : ForwardQActualStarredSpace.StarredInput c,
      normalizeStarred c a z ≠
        patchedStarred c x (fun _ _ => other) := by
  intro z heq
  have ha := markedLetter_normalized c i z a
  have hb := markedLetter_patched_constant c i x other
  have hab : a = other := by
    calc
      a = markedLetter c i (normalizeStarred c a z) := ha.symm
      _ = markedLetter c i
          (patchedStarred c x (fun _ _ => other)) :=
        congrArg (markedLetter c i) heq
      _ = other := hb
  exact hne hab

/-- Normalization cannot surject onto the corrected starred
domain when it contains a selected D₂ coordinate and two
distinct letters.  An explicit missed input is supplied. -/
theorem normalizeStarred_not_surjective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c)
    (a other : α)
    (hne : a ≠ other) :
    ¬ Function.Surjective (normalizeStarred c a) := by
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj
    (patchedStarred c x (fun _ _ => other))
  exact (patched_other_letter_not_in_normalization_range
    c i x a other hne z) hz

/-- The clean two-letter version needs only an inhabited
corrected-starred input and one actual selected bullet
coordinate.  There is no assumption of arbitrary bullet
inputs being admissible: the witness is patched from a
genuine element of the corrected W-star subtype. -/
theorem normalizeStarred_not_surjective_of_two_letters
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : MixedProduct.BulletIndex (kind c))
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hα : SpanAudit.HasTwoLetters α)
    (a : α) :
    ¬ Function.Surjective (normalizeStarred c a) := by
  rcases hα with ⟨p, q, hpq⟩
  by_cases hap : a = p
  · exact normalizeStarred_not_surjective c i x a q
      (by simpa [hap] using hpq)
  · exact normalizeStarred_not_surjective c i x a p hap

end DualTree.ForwardQNormalizationObstruction
