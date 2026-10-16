import DualTree.ForwardQFinalProjectionOrder
import DualTree.ForwardCompleteBijection

/-!
# Direction labels for the actual canonical cone projections

The first-branch direction is more information than the
prefix order: a rooted prefix-poset embedding could
permute directions. The corrected forward-complete
canonical embedding is defined by the genuine
directional successor walk and therefore preserves
the first outgoing ambient direction of a support path.

We first prove this on arbitrary bounded source
addresses of a genuine forward-complete ambient
support T, using its rank bound and
CanonicalSupportWalk.walk_first_direction.
Then we apply it to the concrete frontier projection
P_i(z), whose inverse source address is exactly
inverse_T(frontier_i) ++ z.

Thus a local cone relation
    z ++ [dir] prefix w
implies the ACTUAL ambient T cone relation
    P_i(z) ++ [dir] prefix P_i(w).
This remains valid with stretched ambient edges.

This is a necessary ingredient for the full branching
proof of the FINAL glued support T'_M. It does not by
itself prove local immediate edges remain immediate
in T'_M, a retained/new branching condition,
or the full M-complete skew conclusion.
-/

namespace DualTree.ForwardQFinalProjectionDirection

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The corrected complete-skew canonical embedding preserves
the precise FIRST outgoing direction on a pair of bounded
homogeneous source addresses, not merely their prefix order. -/
theorem canonicalEmbedding_childCone_mono
    {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB
      SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k)
    (dir : Fin b)
    (hchild : IsPrefix (u.1 ++ [dir]) v.1) :
    IsPrefix
      ((ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u).1 ++ [dir])
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon v).1 := by
  obtain ⟨tail, htail⟩ := hchild
  have hv : v.1 = u.1 ++ (dir :: tail) := by
    calc
      v.1 = (u.1 ++ [dir]) ++ tail := htail
      _ = u.1 ++ (dir :: tail) := by simp [List.append_assoc]
  have hlength : u.1.length + 1 < k := by
    have hle : (u.1 ++ [dir]).length ≤ v.1.length :=
      prefix_length_le ⟨tail, htail⟩
    simp only [List.length_append, List.length_singleton] at hle
    exact lt_of_le_of_lt hle v.2
  have hbranch : SkewTree.uniqueBranchB T
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u).1 dir = true := by
    apply ForwardCompleteEmbedding.branch_of_height_lt
      T hcomplete hnon
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u).1
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u).2
    rw [ForwardCompleteEmbedding.canonicalEmbedding_height
      T hcomplete hnon u]
    exact hlength
  have hwalk :
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon v).1 =
      CanonicalSupportWalk.walk T
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon u).1
        (dir :: tail) := by
    change CanonicalSupportWalk.walk T
      (ForwardCompleteEmbedding.rootOf T hcomplete hnon) v.1 =
      CanonicalSupportWalk.walk T
        (CanonicalSupportWalk.walk T
          (ForwardCompleteEmbedding.rootOf T hcomplete hnon) u.1)
        (dir :: tail)
    rw [hv, CanonicalSupportWalk.walk_append]
  rw [hwalk]
  exact CanonicalSupportWalk.walk_first_direction T
    (ForwardCompleteEmbedding.canonicalEmbedding
      T hcomplete hnon u).1 dir tail hbranch

/-- Every actual corrected frontier cone projection
P_i preserves the labelled first outgoing ambient
direction of local addresses. This theorem uses the
literal certified inverse-address identity for P_i,
not an abstract order isomorphism. -/
theorem projected_childCone_mono
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (dir : Fin b)
    (hchild : IsPrefix (z.1 ++ [dir]) w.1) :
    IsPrefix
      ((projected c ⟨i,z⟩).1 ++ [dir])
      (projected c ⟨i,w⟩).1 := by
  let pz := ForwardQActualCoordinateWord.projectLocal c i z
  let pw := ForwardQActualCoordinateWord.projectLocal c i w
  have hinverse :
      IsPrefix
        ((ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon pz).1 ++ [dir])
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon pw).1 := by
    rw [ForwardQActualCoordinateWord.projectLocal_inverse c i z,
      ForwardQActualCoordinateWord.projectLocal_inverse c i w]
    have h := ConeProjectionAlgebra.prefix_append_left
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt
          c.T c.cut i)).1 hchild
    simpa only [List.append_assoc] using h
  have hdir :=
    canonicalEmbedding_childCone_mono c.T c.hcomplete c.hnon
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon pz)
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon pw)
      dir hinverse
  simpa only [ForwardCompleteBijection.inverse_right]
    using hdir

end DualTree.ForwardQFinalProjectionDirection
