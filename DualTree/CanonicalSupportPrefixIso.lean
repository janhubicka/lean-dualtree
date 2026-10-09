import DualTree.CompleteSupportSurjective

/-!
# The canonical complete-skew map reflects the preAddr order

The complete-skew support embedding is already bijective and
preAddr-preserving. To reflect prefixes, take the preAddr of the
second source address with the same length as the first.
Both its image and the image of the first address are support
prefixes of the same target with identical intrinsic heights,
so they coincide by the support-rank path uniqueness theorem.
Injectivity then identifies their source addresses.

This gives an isomorphism of rooted preAddr trees between b^{<k}
and the k-complete skew support T, without any claim about the
paper's printed auxiliary linear order (which has a separate
counterexample).
-/

namespace DualTree.CanonicalSupportPrefixIso

/-- A support preAddr cannot have greater intrinsic height than
its support extension. -/
theorem heightAt_le_of_prefix {b : Nat}
    (T : List (Node b)) {s t : Node b}
    (hs : s ∈ T) (hst : IsPrefix s t) :
    SkewTree.heightAt T s ≤ SkewTree.heightAt T t := by
  by_cases heq : s = t
  · simp [heq]
  · exact Nat.le_of_lt
      (SupportHeightRanks.heightAt_lt_of_strictPrefix
        T hs ⟨hst, heq⟩)

/-- The canonical map on b^{<k} reflects ambient initial segments. -/
theorem canonicalEmbedding_prefix_reflect {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u v : BoundedNode b k)
    (himage : IsPrefix
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1) :
    IsPrefix u.1 v.1 := by
  let I := CompleteSupportAddresses.canonicalEmbedding T hcomplete
  have hle : u.1.length ≤ v.1.length := by
    have hrank : SkewTree.heightAt T (I u).1 ≤
        SkewTree.heightAt T (I v).1 :=
      heightAt_le_of_prefix T (I u).2 himage
    change SkewTree.heightAt T
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1 ≤
      SkewTree.heightAt T
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 at hrank
    rw [CompleteSupportAddresses.canonicalEmbedding_height T hcomplete u,
      CompleteSupportAddresses.canonicalEmbedding_height T hcomplete v] at hrank
    exact hrank
  have htakeLength :
      (v.1.take u.1.length).length = u.1.length := by
    simp [List.length_take, Nat.min_eq_left hle]
  have htakeBound : InHomTree k (v.1.take u.1.length) := by
    change (v.1.take u.1.length).length < k
    rw [htakeLength]
    exact u.2
  let preAddr : BoundedNode b k :=
    ⟨v.1.take u.1.length, htakeBound⟩
  have hpv : IsPrefix preAddr.1 v.1 := by
    refine ⟨v.1.drop u.1.length, ?_⟩
    exact (List.take_append_drop u.1.length v.1).symm
  have hIpv : IsPrefix (I preAddr).1 (I v).1 :=
    CompleteSupportAddresses.canonicalEmbedding_prefix
      T hcomplete preAddr v hpv
  have heqRank : SkewTree.heightAt T (I u).1 =
      SkewTree.heightAt T (I preAddr).1 := by
    rw [CompleteSupportAddresses.canonicalEmbedding_height T hcomplete u,
      CompleteSupportAddresses.canonicalEmbedding_height T hcomplete preAddr]
    exact htakeLength.symm
  have heqImage : (I u).1 = (I preAddr).1 :=
    SupportHeightRanks.heightAt_injective_on_common_path
      T (I u).2 (I preAddr).2 himage hIpv heqRank
  have heqSource : u = preAddr :=
    (CanonicalSupportInjective.canonicalEmbedding_injective T hcomplete)
      (Subtype.ext heqImage)
  have huval : u.1 = preAddr.1 := congrArg Subtype.val heqSource
  rw [huval]
  exact hpv

/-- The canonical embedding is an isomorphism of preAddr trees. -/
theorem canonicalEmbedding_prefix_iff {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u v : BoundedNode b k) :
    IsPrefix u.1 v.1 ↔
      IsPrefix
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 := by
  constructor
  · exact CompleteSupportAddresses.canonicalEmbedding_prefix
      T hcomplete u v
  · exact canonicalEmbedding_prefix_reflect T hcomplete u v

/-- Canonical inverse addresses inherit the preAddr relation on T. -/
theorem inverseAddress_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (s t : {u : Node b // u ∈ T})
    (hst : IsPrefix s.1 t.1) :
    IsPrefix
      (CompleteSupportSurjective.inverseAddress T hcomplete s).1
      (CompleteSupportSurjective.inverseAddress T hcomplete t).1 := by
  apply (canonicalEmbedding_prefix_iff T hcomplete
    (CompleteSupportSurjective.inverseAddress T hcomplete s)
    (CompleteSupportSurjective.inverseAddress T hcomplete t)).2
  simpa [CompleteSupportSurjective.inverse_right] using hst

end DualTree.CanonicalSupportPrefixIso
