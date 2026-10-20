import DualTree.ForwardQFinalUnsafeOutputConstant
import DualTree.ForwardCompleteBijection

/-!
# Prefix reflection for the canonical complete-support inverse

The inverse of the finite canonical complete-skew support embedding
must preserve the actual prefix relation on complete-support vertices.
This is needed when a frontier is below a T-node: the inverse address
of the node then splits as frontier inverse address followed by its
genuine local tail.

The proof deliberately does not assume a new tree-order isomorphism.
It uses the already verified path-reachability theorem and uniqueness
of admissible support walks; concatenating an admissible tail at the
appropriate endpoint yields the exact inverse-prefix equation.

It is independent of Q symbol or starred-output reconstruction.
-/

namespace DualTree.ForwardQFinalUnsafeSamplerGeometry

/-- Concatenating two genuinely admissible support traversals yields
an admissible traversal from the original starting vertex. -/
theorem admissible_append
    {b : Nat} (T : List (Node b))
    (s x y : Node b)
    (hx : CanonicalSupportWalk.Admissible T s x)
    (hy : CanonicalSupportWalk.Admissible T
      (CanonicalSupportWalk.walk T s x) y) :
    CanonicalSupportWalk.Admissible T s (x ++ y) := by
  induction x generalizing s with
  | nil =>
      simpa [CanonicalSupportWalk.walk] using hy
  | cons i xs ih =>
      rcases hx with ⟨hi,hxs⟩
      change SkewTree.uniqueBranchB T s i = true ∧
        CanonicalSupportWalk.Admissible T
          (CanonicalSupportWalk.next T s i) (xs ++ y)
      exact ⟨hi, ih (CanonicalSupportWalk.next T s i) hxs hy⟩

/-- The canonical inverse of the actual nonsingleton complete
forward-skew support respects EVERY genuine ambient prefix between
support nodes.  No synthetic immediate ambient-child assumption. -/
theorem inverseAddress_preserves_prefix
    {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s t : {u : Node b // u ∈ T})
    (hst : IsPrefix s.1 t.1) :
    IsPrefix
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon s).1
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon t).1 := by
  let root := ForwardCompleteEmbedding.rootOf T hcomplete hnon
  let x := ForwardCompleteBijection.inverseAddress T hcomplete hnon s
  let y := ForwardCompleteBijection.inverseAddress T hcomplete hnon t
  have hx : CanonicalSupportWalk.Admissible T root x.1 :=
    (ForwardCompleteEmbedding.canonical_bounded_address
      T hcomplete hnon x.1 x.2).1
  have hy : CanonicalSupportWalk.Admissible T root y.1 :=
    (ForwardCompleteEmbedding.canonical_bounded_address
      T hcomplete hnon y.1 y.2).1
  have hwalkx : CanonicalSupportWalk.walk T root x.1 = s.1 :=
    congrArg Subtype.val
      (ForwardCompleteBijection.inverse_right T hcomplete hnon s)
  have hwalky : CanonicalSupportWalk.walk T root y.1 = t.1 :=
    congrArg Subtype.val
      (ForwardCompleteBijection.inverse_right T hcomplete hnon t)
  obtain ⟨tail, htailValid, hwalkTail⟩ :=
    ForwardCompleteBijection.walk_address_of_prefix_forward
      T hcomplete hnon s.1 t.1 s.2 t.2 hst
  have hvalidTail : CanonicalSupportWalk.Admissible T
      (CanonicalSupportWalk.walk T root x.1) tail := by
    rw [hwalkx]
    exact htailValid
  have hvalidConcat :
      CanonicalSupportWalk.Admissible T root (x.1 ++ tail) :=
    admissible_append T root x.1 tail hx hvalidTail
  have hwalkConcat :
      CanonicalSupportWalk.walk T root (x.1 ++ tail) = t.1 := by
    calc
      CanonicalSupportWalk.walk T root (x.1 ++ tail) =
          CanonicalSupportWalk.walk T
            (CanonicalSupportWalk.walk T root x.1) tail :=
        CanonicalSupportWalk.walk_append T root x.1 tail
      _ = CanonicalSupportWalk.walk T s.1 tail := by rw [hwalkx]
      _ = t.1 := hwalkTail
  have hexact : x.1 ++ tail = y.1 :=
    CanonicalSupportInjective.walk_injective_of_admissible
      T (x.1 ++ tail) root y.1
        hvalidConcat hy (hwalkConcat.trans hwalky.symm)
  exact ⟨tail, hexact.symm⟩

end DualTree.ForwardQFinalUnsafeSamplerGeometry
