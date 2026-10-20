import DualTree.ForwardQFinalUnsafeSamplerGeometry
import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQFinalSafeAddressLookup

/-!
# Reconstruct a true projected cone address from a short inverse tail

The actual forward-complete inverse maps support-prefix pairs to
source-address-prefix pairs.  Thus a T-node inside one genuine
outside-cut frontier cone has an inverse word equal to the frontier
inverse followed by its canonical local tail.

If that tail is inside the shortened mixed coordinate height,
the already verified projectLocal inverse law and the complete-support
bijection force the node to equal P_i(z).  In particular a node
with NO safe local address has an out-of-range inverse tail in any
selected frontier cone, so the literal Q input sampler uses fallback.

The results are about the actual shortened domain and do not assume
the stronger, inapplicable original paper's local height.
-/

namespace DualTree.ForwardQFinalUnsafeConeReconstruction

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalUnsafeSamplerGeometry

/-- A genuine T vertex above the sorted frontier whose inverse local
tail fits the shortened height equals one of the ACTUAL projections
P_i(z), as dependent support vertices (not merely nodes in a cone). -/
theorem projected_eq_of_short_inverse_tail
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c)
    (t : {u : Node b // u ∈ c.T})
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hshort : InHomTree (k - (m + 1))
      (ForwardQActualCoordinateWord.tailOfTNode c i t)) :
    ∃ z : BoundedNode b (k - (m + 1)),
      ForwardQActualCoordinateWord.projectLocal c i z = t := by
  let front := ForwardOrderedProjections.frontierAt c.T c.cut i
  let x := ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon front
  let y := ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon t
  let z : BoundedNode b (k - (m + 1)) :=
    ⟨ForwardQActualCoordinateWord.tailOfTNode c i t,hshort⟩
  obtain ⟨tail, htail⟩ :=
    inverseAddress_preserves_prefix
      c.T c.hcomplete c.hnon front t hfront
  have hdrop :
      ForwardQActualCoordinateWord.tailOfTNode c i t = tail := by
    change y.1.drop x.1.length = tail
    rw [htail]
    simp
  have hinv :
      (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
        (ForwardQActualCoordinateWord.projectLocal c i z)).1 =
        y.1 := by
    calc
      _ = x.1 ++ z.1 :=
        ForwardQActualCoordinateWord.projectLocal_inverse c i z
      _ = x.1 ++ tail := congrArg (List.append x.1) hdrop
      _ = y.1 := htail.symm
  have hinvEq :
      ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
        (ForwardQActualCoordinateWord.projectLocal c i z) = y :=
    Subtype.ext hinv
  have heq : ForwardQActualCoordinateWord.projectLocal c i z = t := by
    calc
      ForwardQActualCoordinateWord.projectLocal c i z =
          ForwardCompleteEmbedding.canonicalEmbedding
            c.T c.hcomplete c.hnon
            (ForwardCompleteBijection.inverseAddress
              c.T c.hcomplete c.hnon
              (ForwardQActualCoordinateWord.projectLocal c i z)) :=
        (ForwardCompleteBijection.inverse_right
          c.T c.hcomplete c.hnon
          (ForwardQActualCoordinateWord.projectLocal c i z)).symm
      _ = ForwardCompleteEmbedding.canonicalEmbedding
          c.T c.hcomplete c.hnon y :=
        congrArg (ForwardCompleteEmbedding.canonicalEmbedding
          c.T c.hcomplete c.hnon) hinvEq
      _ = t :=
        ForwardCompleteBijection.inverse_right c.T c.hcomplete c.hnon t
  exact ⟨z,heq⟩

/-- If the actual safe projection decoder returns none, any selected
frontier cone containing the node has a tail OUTSIDE the shortened
local word domain. This is the missing fallback-side geometric fact. -/
theorem no_safe_implies_tail_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c)
    (t : {u : Node b // u ∈ c.T})
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hnone : ForwardQFinalSafeAddressLookup.safeAddress c t.1 = none) :
    ¬ InHomTree (k - (m + 1))
      (ForwardQActualCoordinateWord.tailOfTNode c i t) := by
  intro hshort
  obtain ⟨z,heq⟩ :=
    projected_eq_of_short_inverse_tail c i t hfront hshort
  have hSome :
      ForwardQFinalSafeAddressLookup.safeAddress c t.1 =
        some (⟨i,z⟩ : LocalAddress c) := by
    rw [← heq]
    exact ForwardQFinalSafeAddressLookup.safeAddress_projected c ⟨i,z⟩
  rw [hnone] at hSome
  cases hSome

/-- The actual enlarged-letter Q sampler returns the literal
fallback at an unsafe node in a selected frontier cone, including
the case when a frontier exists but its inverse tail is too long. -/
theorem sampledEnlarged_fallback_of_no_safe
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c)
    (i : ForwardQFullFrontierWord.Index c)
    (t : BoundedNode b n)
    (ht : t.1 ∈ c.T)
    (hfront : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (hnone : ForwardQFinalSafeAddressLookup.safeAddress c t.1 = none) :
    ForwardQEnlargedConstantWords.sampledEnlarged
      c w fallback i t = Sum.inl fallback := by
  have hnot :
      ¬ InHomTree (k - (m + 1))
        (ForwardQActualCoordinateWord.tailOfTNode
          c i ⟨t.1,ht⟩) :=
    no_safe_implies_tail_outside c i ⟨t.1,ht⟩ hfront hnone
  simp [ForwardQEnlargedConstantWords.sampledEnlarged, ht, hnot]

end DualTree.ForwardQFinalUnsafeConeReconstruction
