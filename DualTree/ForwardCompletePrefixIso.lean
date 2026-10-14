import DualTree.ForwardCompleteBijection
import DualTree.CanonicalSupportPrefixIso

/-!
# A prefix-order isomorphism for forward-complete skew supports

The published reverse-lex auxiliary order is not the forward order
needed by the repaired Lemma 27 construction.  Consequently the old
CanonicalSupportPrefixIso theorem (with the assumption
completeB paperAuxB k T) cannot simply be applied to a
completeB forwardAuxB k T support.

This module proves the analogous statements for the ACTUAL corrected
canonical embedding I_T and its chosen inverse.  The argument is
purely intrinsic: ranks increase strictly along support prefixes,
a prefix of a fixed rank on a support branch is unique, and I_T
preserves prefixes and intrinsic ranks and is injective.

In particular, for s,t in T, their inverse support addresses are
prefix-comparable in exactly the same way as s,t.  This will allow
membership in a projected Q marked cone to be transported to a
local-address prefix test in subsequent Lemma 27 colour transport.

No printed-order completeness or simplicity assumption occurs here.
-/

namespace DualTree.ForwardCompletePrefixIso

/-- The forward-complete canonical embedding also REFLECTS
the ambient prefix relation, not only preserves it. -/
theorem canonicalEmbedding_prefix_reflect {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k)
    (himage : IsPrefix
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u).1
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon v).1) :
    IsPrefix u.1 v.1 := by
  let I := ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon
  have hle : u.1.length ≤ v.1.length := by
    have hrank : SkewTree.heightAt T (I u).1 ≤
        SkewTree.heightAt T (I v).1 :=
      CanonicalSupportPrefixIso.heightAt_le_of_prefix
        T (I u).2 himage
    change SkewTree.heightAt T
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon u).1 ≤
      SkewTree.heightAt T
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon v).1 at hrank
    rw [ForwardCompleteEmbedding.canonicalEmbedding_height
          T hcomplete hnon u,
        ForwardCompleteEmbedding.canonicalEmbedding_height
          T hcomplete hnon v] at hrank
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
    ForwardCompleteEmbedding.canonicalEmbedding_prefix
      T hcomplete hnon preAddr v hpv
  have heqRank : SkewTree.heightAt T (I u).1 =
      SkewTree.heightAt T (I preAddr).1 := by
    rw [ForwardCompleteEmbedding.canonicalEmbedding_height
          T hcomplete hnon u,
        ForwardCompleteEmbedding.canonicalEmbedding_height
          T hcomplete hnon preAddr]
    exact htakeLength.symm
  have heqImage : (I u).1 = (I preAddr).1 :=
    SupportHeightRanks.heightAt_injective_on_common_path
      T (I u).2 (I preAddr).2 himage hIpv heqRank
  have heqSource : u = preAddr :=
    (ForwardCompleteEmbedding.canonicalEmbedding_injective
      T hcomplete hnon) (Subtype.ext heqImage)
  have huval : u.1 = preAddr.1 := congrArg Subtype.val heqSource
  rw [huval]
  exact hpv

/-- True two-way prefix preservation for forward-complete
supports, independent of their printed reverse-lex status. -/
theorem canonicalEmbedding_prefix_iff {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k) :
    IsPrefix u.1 v.1 ↔
      IsPrefix
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon u).1
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon v).1 := by
  constructor
  · exact ForwardCompleteEmbedding.canonicalEmbedding_prefix
      T hcomplete hnon u v
  · exact canonicalEmbedding_prefix_reflect T hcomplete hnon u v

/-- Inverse support addresses preserve prefixes in the
corrected forward-complete setting. -/
theorem inverseAddress_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s t : {u : Node b // u ∈ T})
    (hst : IsPrefix s.1 t.1) :
    IsPrefix
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon s).1
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1 := by
  apply (canonicalEmbedding_prefix_iff T hcomplete hnon
    (ForwardCompleteBijection.inverseAddress T hcomplete hnon s)
    (ForwardCompleteBijection.inverseAddress T hcomplete hnon t)).2
  simpa [ForwardCompleteBijection.inverse_right] using hst

/-- Prefix order on T is EQUIVALENT to prefix order on
the genuine corrected inverse-support addresses. -/
theorem inverseAddress_prefix_iff {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s t : {u : Node b // u ∈ T}) :
    IsPrefix
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon s).1
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon t).1 ↔
      IsPrefix s.1 t.1 := by
  constructor
  · intro hpre
    have hp := ForwardCompleteEmbedding.canonicalEmbedding_prefix
      T hcomplete hnon
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon s)
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon t)
      hpre
    simpa [ForwardCompleteBijection.inverse_right] using hp
  · exact inverseAddress_prefix T hcomplete hnon s t

end DualTree.ForwardCompletePrefixIso
