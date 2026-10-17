import DualTree.ForwardQFinalProjectedChildConverse
import DualTree.ForwardQFinalProjectionDirection
import DualTree.ForwardQFinalProjectionOrder

/-!
# Exact first-direction reflection for corrected frontier projections

An abstract isomorphism of rooted prefix orders need not
preserve the labelled outgoing directions. The genuine
forward-complete canonical projection P_i, however, is
constructed by a labelled directional support walk.
The earlier lemma proves P_i PRESERVES outgoing direction.

Here we prove the converse: whenever P_i(w) lies in a
particular first ambient direction cone above P_i(z),
then w lies in the SAME local direction cone above z.

The proof first reflects the underlying prefix order,
giving w=z++tail. The tail cannot be empty because the
projected child cone has greater ambient length than the
projected parent. Its first letter j projects into the
j-cone by the already verified direction-preserving lemma.
Two one-letter cones based at P_i(z) cannot both contain
the same descendant unless their letters coincide, hence
j is the requested direction.

This reflection is valid for stretched ambient support
edges and requires no complete-skew hypothesis on the
FINAL union T'_M. It will be used to transport uniqueness
of same-direction local support successors to the glued
final support.
-/

namespace DualTree.ForwardQFinalProjectionDirectionReflect

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The actual frontier projection preserves AND reflects
the exact first outgoing ambient direction on all its
uniformly safe bounded local tail addresses. -/
theorem projected_childCone_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (dir : Fin b) :
    IsPrefix (z.1 ++ [dir]) w.1 ↔
    IsPrefix
      ((projected c ⟨i,z⟩).1 ++ [dir])
      (projected c ⟨i,w⟩).1 := by
  constructor
  · exact
      ForwardQFinalProjectionDirection.projected_childCone_mono
        c i z w dir
  · intro hcone
    have hproj : IsPrefix (projected c ⟨i,z⟩).1
        (projected c ⟨i,w⟩).1 :=
      isPrefix_trans ⟨[dir],rfl⟩ hcone
    have hlocal : IsPrefix z.1 w.1 :=
      (ForwardQFinalProjectionOrder.projected_same_frontier_prefix_iff
        c i z w).1 hproj
    obtain ⟨tail,htail⟩ := hlocal
    cases tail with
    | nil =>
        have hEq : z = w := Subtype.ext (by simpa using htail.symm)
        subst w
        have hlen := prefix_length_le hcone
        simp only [List.length_append,List.length_singleton] at hlen
        omega
    | cons j rest =>
        have hlocalJ : IsPrefix (z.1 ++ [j]) w.1 :=
          ⟨rest,by simpa [List.append_assoc] using htail⟩
        have hprojectJ :
            IsPrefix
              ((projected c ⟨i,z⟩).1 ++ [j])
              (projected c ⟨i,w⟩).1 :=
          ForwardQFinalProjectionDirection.projected_childCone_mono
            c i z w j hlocalJ
        have hcomparison :
            IsPrefix
              ((projected c ⟨i,z⟩).1 ++ [dir])
              ((projected c ⟨i,z⟩).1 ++ [j]) :=
          CutFrontier.prefix_of_prefix_length_le
            hcone hprojectJ (by simp)
        have hwords :
            (projected c ⟨i,z⟩).1 ++ [dir] =
            (projected c ⟨i,z⟩).1 ++ [j] :=
          CutPreservation.prefix_eq_of_length_eq
            hcomparison (by simp)
        have hdrop := congrArg
          (fun u : Node b =>
            u.drop (projected c ⟨i,z⟩).1.length) hwords
        have hdirEq : dir = j := by
          have hsingle : [dir] = [j] := by simpa using hdrop
          simpa using hsingle
        subst j
        exact hlocalJ

end DualTree.ForwardQFinalProjectionDirectionReflect
