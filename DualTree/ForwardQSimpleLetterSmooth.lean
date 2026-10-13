import DualTree.ForwardQAmbientFibreSpan
import DualTree.ForwardQStarredSmoothPartitions

/-!
# A verified simplicity-to-smoothness case for the genuine fibrewise Q

Definition 24 has a witness partition A = B₁ ⊔ B₂.  This module settles
the case B₂ = ∅ on the *actual* corrected Lemma 27 fibrewise Q output.

Here "simple" is scoped to the original ambient f, as in the paper:
both starred outputs must refine f (support containment and evaluated
span containment).  With B₂ empty, simplicity requires agreement of
the full words and equality of their interior vertex sets, but makes
NO demand that their leaves, marked points, or whole tree supports agree.

For the corrected forward-order mixed product, choose Γ₁ to contain
every selected D₂ coordinate.  Smooth-related enlarged inputs then
have identical coordinate WORDS, although their D₂ marked points may
move.  The genuine ambient-fibrewise Q decoder depends only on those
words (not the marked points), while the Q interior is always the
original source interior.  Consequently the simple colouring pulled
back along Q is smooth; the classwise extension lemma produces a
TOTAL smooth colouring of the full enlarged mixed product.

This closes one genuine special case of the missing Definition 24
transport.  It does NOT handle B₂ ≠ ∅, where the colour may observe
selected Q marked points and ignore only the corresponding successor
cones.  Nor does it supply the final mixed-product Ramsey refinement,
the original printed auxiliary-order assertion, or Lemma 28.
-/

namespace DualTree.ForwardQSimpleLetterSmooth

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord

/-- The sampled enlarged letter depends only on the coordinate words,
not on any D₂ marked point or D₁ leaf. -/
theorem sampled_eq_of_words
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c)
    (hw : ∀ i, x.words i = y.words i)
    (i : ForwardQAmbientFibreSymbol.Index
      ({ core := c
         ambient := (by assumption)
         ambient_support_T := (by assumption)
         T_bounded := (by assumption)
         substitution := (by assumption)
         source_substitution := (by assumption) } :
       FibreFrame b n l k m α))
    (t : BoundedNode b n) :
    ForwardQEnlargedConstantWords.sampledEnlarged c x fallback i t =
      ForwardQEnlargedConstantWords.sampledEnlarged c y fallback i t := by
  classical
  have heq : x.words = y.words := funext hw
  simp [ForwardQEnlargedConstantWords.sampledEnlarged, heq]

end DualTree.ForwardQSimpleLetterSmooth
