import DualTree.CanonicalSupportPrefixIso

/-!
# Actual canonical cone coordinates on their bounded intrinsic domains

For a complete skew support T, the canonical map b^{<k} → T and its
inverse are now verified. For a specified support vertex t, take the
canonical source address s = I_T^{-1}(t). A tail z is admissible for
the intrinsic cone exactly when |s| + |z| < k.

The following typed projection sends z to I_T(s ++ z), with no
unbounded appeal to the paper's printed P_i formula. It fixes the
root t, preserves prefixes and intrinsic levels, and the canonical
inverse recovers s ++ z exactly.

This certifies the actual cone geometry on its *intrinsic* domain.
Lemma 27 also uses larger ambient tails in b^{<N}, which require a
separate domain extension or modification of the mixed-product
parameters. This module does not claim that larger printed domain.
-/

namespace DualTree.CanonicalConeCoordinates

/-- Tails which fit after the canonical source address of t. -/
abbrev SourceTail {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :=
  {z : Node b //
    (CompleteSupportSurjective.inverseAddress T hcomplete t).1.length +
      z.length < k}

/-- The complete source address obtained by joining the root address
to a tail inside its certified intrinsic domain. -/
noncomputable def address {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) : BoundedNode b k :=
  ⟨(CompleteSupportSurjective.inverseAddress T hcomplete t).1 ++ z.1, by
    change
      ((CompleteSupportSurjective.inverseAddress T hcomplete t).1 ++ z.1).length < k
    simpa only [List.length_append] using z.2⟩

/-- The actual complete-skew cone projection on a well-typed tail. -/
noncomputable def project {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) :
    {u : Node b // u ∈ T} :=
  CompleteSupportAddresses.canonicalEmbedding T hcomplete
    (address T hcomplete t z)

/-- The empty tail belongs to every canonical cone. -/
noncomputable def emptyTail {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    SourceTail T hcomplete t :=
  ⟨[], by
    have hb := (CompleteSupportSurjective.inverseAddress T hcomplete t).2
    simpa [InHomTree] using hb⟩

/-- The constructed source address of the empty tail is exactly I_T^{-1}(t). -/
theorem address_empty {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    address T hcomplete t (emptyTail T hcomplete t) =
      CompleteSupportSurjective.inverseAddress T hcomplete t := by
  apply Subtype.ext
  simp [address, emptyTail]

/-- The cone projection sends its empty tail exactly to the frontier t. -/
theorem project_empty {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    project T hcomplete t (emptyTail T hcomplete t) = t := by
  unfold project
  rw [address_empty]
  exact CompleteSupportSurjective.inverse_right T hcomplete t

/-- A canonical cone projection preserves the initial-segment relation. -/
theorem project_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (x y : SourceTail T hcomplete t)
    (hxy : IsPrefix x.1 y.1) :
    IsPrefix (project T hcomplete t x).1
      (project T hcomplete t y).1 := by
  have hsrc :
      IsPrefix (address T hcomplete t x).1
        (address T hcomplete t y).1 :=
    ConeProjectionAlgebra.prefix_append_left
      (CompleteSupportSurjective.inverseAddress T hcomplete t).1 hxy
  exact CompleteSupportAddresses.canonicalEmbedding_prefix
    T hcomplete (address T hcomplete t x)
      (address T hcomplete t y) hsrc

/-- Every projected tail lies in the ambient prefix cone above t. -/
theorem project_cone {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) :
    IsPrefix t.1 (project T hcomplete t z).1 := by
  have hsrc :
      IsPrefix
        (CompleteSupportSurjective.inverseAddress T hcomplete t).1
        (address T hcomplete t z).1 :=
    ⟨z.1, rfl⟩
  have hp :=
    CompleteSupportAddresses.canonicalEmbedding_prefix
      T hcomplete
      (CompleteSupportSurjective.inverseAddress T hcomplete t)
      (address T hcomplete t z) hsrc
  have hright :
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (CompleteSupportSurjective.inverseAddress T hcomplete t)).1 = t.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete t)
  rw [hright] at hp
  exact hp

/-- Projecting a tail advances the intrinsic rank by its length. -/
theorem project_height {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) :
    SkewTree.heightAt T (project T hcomplete t z).1 =
      SkewTree.heightAt T t.1 + z.1.length := by
  have hrank :=
    CompleteSupportAddresses.canonicalEmbedding_height
      T hcomplete (address T hcomplete t z)
  change SkewTree.heightAt T (project T hcomplete t z).1 =
    (address T hcomplete t z).1.length at hrank
  have hsource :
      (CompleteSupportSurjective.inverseAddress T hcomplete t).1.length =
        SkewTree.heightAt T t.1 :=
    CompleteSupportSurjective.inverse_length T hcomplete t
  simp only [address, List.length_append] at hrank
  omega

/-- The actual canonical inverse recovers the complete source address
of any projected tail. -/
theorem inverse_project {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) :
    CompleteSupportSurjective.inverseAddress T hcomplete
        (project T hcomplete t z) =
      address T hcomplete t z :=
  CompleteSupportSurjective.inverse_left T hcomplete
    (address T hcomplete t z)

/-- In particular the inverse of a projected point has the
literal concatenated source coordinates used in Lemma 27. -/
theorem inverse_project_tail {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T})
    (z : SourceTail T hcomplete t) :
    (CompleteSupportSurjective.inverseAddress T hcomplete
      (project T hcomplete t z)).1 =
      (CompleteSupportSurjective.inverseAddress T hcomplete t).1 ++ z.1 := by
  have h := congrArg Subtype.val (inverse_project T hcomplete t z)
  simpa [address] using h

end DualTree.CanonicalConeCoordinates
