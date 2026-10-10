import DualTree.ForwardCompleteBijection
import DualTree.ConeProjectionAlgebra

/-!
# Canonical cone projections for genuinely forward-complete supports

The original Lemma 27 cone map P_i(z) is described through the
canonical embedding I_T. The previously formalized
CanonicalConeCoordinates uses *printed-order complete skew*
supports and is not a valid replacement for the corrected
global forward-auxiliary convention.

This file constructs the actual bounded cone projection for a
nonsingleton support satisfying
`completeB forwardAuxB k T = true`.
For t in T and a local tail z, its canonical source address is
I_T^{-1}(t) ++ z, and the exact admissibility condition is

       |I_T^{-1}(t)| + |z| < k.

The projected support node:
* extends t along the ambient prefix order;
* preserves relative prefix order of local tails;
* has intrinsic height h_T(t)+|z|;
* has inverse canonical address I_T^{-1}(t) ++ z;
* fixes t at the empty tail.

These statements are proved using the true *forward-complete*
bijection, with no appeal to the printed-order constructor.
They certify the cone geometry but do not by themselves
prove that arbitrary points of the original mixed product
have well-typed tails. That needs the same frontier-rank
budget correction and Ramsey parameter changes as before.
-/

namespace DualTree.ForwardCanonicalConeCoordinates

/-- The actual bounded domain of a local tail rooted at a
frontier node in a genuinely forward-complete skew support. -/
abbrev SourceTail {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :=
  {z : Node b //
    (ForwardCompleteBijection.inverseAddress
      T hcomplete hnon t).1.length + z.length < k}

/-- Source address obtained by prefixing the local tail
with the inverse complete-support address of t. -/
noncomputable def address {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) : BoundedNode b k :=
  ⟨(ForwardCompleteBijection.inverseAddress
       T hcomplete hnon t).1 ++ z.1, by
    change
      ((ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1 ++ z.1).length < k
    simpa only [List.length_append] using z.2⟩

/-- Actual forward-complete cone map, including proof that
the image belongs to T. -/
noncomputable def project {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) :
    {u : Node b // u ∈ T} :=
  ForwardCompleteEmbedding.canonicalEmbedding
    T hcomplete hnon (address T hcomplete hnon t z)

/-- The empty tail is admissible at every support vertex. -/
noncomputable def emptyTail {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :
    SourceTail T hcomplete hnon t :=
  ⟨[], by
    have hb := (ForwardCompleteBijection.inverseAddress
      T hcomplete hnon t).2
    simpa [InHomTree] using hb⟩

/-- The address of the empty tail is exactly the
inverse canonical source address of t. -/
theorem address_empty {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :
    address T hcomplete hnon t (emptyTail T hcomplete hnon t) =
      ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t := by
  apply Subtype.ext
  simp [address, emptyTail]

/-- The empty local tail projects to exactly its root t. -/
theorem project_empty {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :
    project T hcomplete hnon t
      (emptyTail T hcomplete hnon t) = t := by
  unfold project
  rw [address_empty]
  exact ForwardCompleteBijection.inverse_right T hcomplete hnon t

/-- Prefix comparable local tails project to prefix
comparable ambient support nodes. -/
theorem project_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (x y : SourceTail T hcomplete hnon t)
    (hxy : IsPrefix x.1 y.1) :
    IsPrefix
      (project T hcomplete hnon t x).1
      (project T hcomplete hnon t y).1 := by
  have hsrc :
      IsPrefix (address T hcomplete hnon t x).1
        (address T hcomplete hnon t y).1 :=
    ConeProjectionAlgebra.prefix_append_left
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1 hxy
  exact ForwardCompleteEmbedding.canonicalEmbedding_prefix
    T hcomplete hnon
    (address T hcomplete hnon t x)
    (address T hcomplete hnon t y) hsrc

/-- Every local projection lies in the ambient support cone
above its designated frontier. -/
theorem project_cone {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) :
    IsPrefix t.1
      (project T hcomplete hnon t z).1 := by
  have hsrc :
      IsPrefix
        (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon t).1
        (address T hcomplete hnon t z).1 :=
    ⟨z.1, rfl⟩
  have hp :=
    ForwardCompleteEmbedding.canonicalEmbedding_prefix
      T hcomplete hnon
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t)
      (address T hcomplete hnon t z) hsrc
  have hright :
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon
        (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon t)).1 = t.1 :=
    congrArg Subtype.val
      (ForwardCompleteBijection.inverse_right
        T hcomplete hnon t)
  rw [hright] at hp
  exact hp

/-- The projected local tail advances the intrinsic support
rank of its frontier by precisely the tail length. -/
theorem project_height {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) :
    SkewTree.heightAt T
      (project T hcomplete hnon t z).1 =
      SkewTree.heightAt T t.1 + z.1.length := by
  have hrank :=
    ForwardCompleteEmbedding.canonicalEmbedding_height
      T hcomplete hnon (address T hcomplete hnon t z)
  change SkewTree.heightAt T
    (project T hcomplete hnon t z).1 =
    (address T hcomplete hnon t z).1.length at hrank
  have hinverse :
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1.length =
        SkewTree.heightAt T t.1 :=
    ForwardCompleteBijection.inverse_length T hcomplete hnon t
  simp only [address, List.length_append] at hrank
  omega

/-- Applying the corrected canonical inverse to a
projected point retrieves the full source address. -/
theorem inverse_project {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) :
    ForwardCompleteBijection.inverseAddress
        T hcomplete hnon (project T hcomplete hnon t z) =
      address T hcomplete hnon t z :=
  ForwardCompleteBijection.inverse_left
    T hcomplete hnon (address T hcomplete hnon t z)

/-- Inverse addresses of projected tails have precisely
the concatenation form used in the repaired Q map. -/
theorem inverse_project_tail {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete hnon t) :
    (ForwardCompleteBijection.inverseAddress
      T hcomplete hnon
      (project T hcomplete hnon t z)).1 =
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1 ++ z.1 := by
  have h := congrArg Subtype.val
    (inverse_project T hcomplete hnon t z)
  simpa [address] using h

end DualTree.ForwardCanonicalConeCoordinates
