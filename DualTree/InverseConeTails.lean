import DualTree.UniformConeDomains
import DualTree.CanonicalSupportPrefixIso

/-!
# Recovering local cone addresses from support vertices

The corrected Lemma 27 coding needs both directions of P_i:
a local address z is sent into the support cone, but conversely
one must recognise the local z corresponding to a support variable
root t within that cone. The previously formalised projection has
a concatenated inverse-address identity.

Here we construct z explicitly by dropping the inverse address
of the frontier from that of t. Prefix reflection makes this
decomposition exact, and the intrinsic height difference gives
the precise bound which ensures z belongs to the common local tree.

This supplies an inverse to the genuine cone projection on its
bounded image, without extending the partial domain by default or
asserting the full global Q coding of Lemma 27.
-/

namespace DualTree.InverseConeTails

/-- The unique suffix of the canonical address of a support node
after a prefix frontier, when its rank difference fits in the
uniform shortened common tail domain. -/
noncomputable def relativeTail {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier target : {t : Node b // t ∈ T})
    (_hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    BoundedNode b (k - (m + 1)) := by
  let s := (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1
  let t := (CompleteSupportSurjective.inverseAddress T hcomplete target).1
  have hs := CompleteSupportSurjective.inverse_length T hcomplete frontier
  have ht := CompleteSupportSurjective.inverse_length T hcomplete target
  refine ⟨t.drop s.length, ?_⟩
  change (t.drop s.length).length < k - (m + 1)
  simp only [List.length_drop]
  dsimp only [s, t]
  rw [ht, hs]
  exact hbudget

/-- The relative source address has length equal to the
difference of the intrinsic heights of the two support nodes. -/
theorem relativeTail_length {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier target : {t : Node b // t ∈ T})
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    (relativeTail T hcomplete frontier target hprefix hbudget).1.length =
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 := by
  simp only [relativeTail, List.length_drop]
  rw [CompleteSupportSurjective.inverse_length T hcomplete target,
      CompleteSupportSurjective.inverse_length T hcomplete frontier]

/-- Source coordinates really split as the frontier address followed
by the recovered relative tail. -/
theorem relativeTail_address {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier target : {t : Node b // t ∈ T})
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    (CompleteSupportSurjective.inverseAddress T hcomplete target).1 =
      (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++
        (relativeTail T hcomplete frontier target hprefix hbudget).1 := by
  have hp : IsPrefix
      (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1
      (CompleteSupportSurjective.inverseAddress T hcomplete target).1 :=
    CanonicalSupportPrefixIso.inverseAddress_prefix T hcomplete
      frontier target hprefix
  have htake := CutFrontier.take_length_of_prefix hp
  calc
    (CompleteSupportSurjective.inverseAddress T hcomplete target).1 =
      ((CompleteSupportSurjective.inverseAddress T hcomplete target).1).take
        (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1.length ++
      ((CompleteSupportSurjective.inverseAddress T hcomplete target).1).drop
        (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1.length :=
          (List.take_append_drop _ _).symm
    _ = (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++
      ((CompleteSupportSurjective.inverseAddress T hcomplete target).1).drop
        (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1.length := by
          rw [htake]
    _ = (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++
      (relativeTail T hcomplete frontier target hprefix hbudget).1 := rfl

/-- Canonical inverse addresses separate points of the support. -/
theorem inverseAddress_injective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    Function.Injective
      (CompleteSupportSurjective.inverseAddress T hcomplete) := by
  intro x y heq
  calc
    x = CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (CompleteSupportSurjective.inverseAddress T hcomplete x) :=
      (CompleteSupportSurjective.inverse_right T hcomplete x).symm
    _ = CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (CompleteSupportSurjective.inverseAddress T hcomplete y) := by
      rw [heq]
    _ = y := CompleteSupportSurjective.inverse_right T hcomplete y

/-- Every sufficiently short support descendant of the frontier is
actually reached by its uniquely reconstructed local cone address. -/
theorem projectCommon_reaches_target {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier target : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
      frontier hf
      (relativeTail T hcomplete frontier target hprefix hbudget) = target := by
  have hproj :=
    UniformConeDomains.projectCommon_inverse T hcomplete cut hcut hlevel hm
      frontier hf (relativeTail T hcomplete frontier target hprefix hbudget)
  have hsource :
      (CompleteSupportSurjective.inverseAddress T hcomplete
        (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
          frontier hf (relativeTail T hcomplete frontier target hprefix hbudget))).1 =
      (CompleteSupportSurjective.inverseAddress T hcomplete target).1 := by
    calc
      _ = (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++
          (relativeTail T hcomplete frontier target hprefix hbudget).1 := hproj
      _ = (CompleteSupportSurjective.inverseAddress T hcomplete target).1 :=
        (relativeTail_address T hcomplete frontier target hprefix hbudget).symm
  apply inverseAddress_injective T hcomplete
  exact Subtype.ext hsource

/-- Each certified common cone projection is injective in its tail. -/
theorem projectCommon_injective {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1) :
    Function.Injective
      (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm frontier hf) := by
  intro x y hxy
  have hsource :
      (CompleteSupportSurjective.inverseAddress T hcomplete
        (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
          frontier hf x)).1 =
      (CompleteSupportSurjective.inverseAddress T hcomplete
        (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
          frontier hf y)).1 :=
    congrArg (fun t : {t : Node b // t ∈ T} =>
      (CompleteSupportSurjective.inverseAddress T hcomplete t).1) hxy
  have hconcat :
      (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++ x.1 =
      (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 ++ y.1 := by
    calc
      _ = (CompleteSupportSurjective.inverseAddress T hcomplete
          (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
            frontier hf x)).1 :=
        (UniformConeDomains.projectCommon_inverse
          T hcomplete cut hcut hlevel hm frontier hf x).symm
      _ = (CompleteSupportSurjective.inverseAddress T hcomplete
          (UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
            frontier hf y)).1 := hsource
      _ = _ := UniformConeDomains.projectCommon_inverse
        T hcomplete cut hcut hlevel hm frontier hf y
  have hdrop := congrArg
    (fun z : Node b =>
      z.drop (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1.length)
    hconcat
  apply Subtype.ext
  simpa using hdrop

end DualTree.InverseConeTails
