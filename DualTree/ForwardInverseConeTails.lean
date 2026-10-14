import DualTree.ForwardCompletePrefixIso
import DualTree.ForwardUniformConeDomains
import DualTree.ForwardQActualCoordinateWord

/-!
# Exact safe local addresses on genuine forward-complete Q frontiers

The corrected Lemma 27 uses a forward-complete support T, a cut
of intrinsic height m, and sorted minimal outside-cut frontiers.
Every T-node t above one of these frontiers has a unique source
address q = I_T^{-1}(t). The new forward-complete prefix isomorphism
shows that a = I_T^{-1}(frontier) is a prefix of q.

If the intrinsic difference rank(t)-rank(frontier) is less than the
common safe local height k-(m+1), the suffix q.drop a.length is a
genuine bounded mixed-product tail z, and the REAL corrected
canonical projection P_frontier(z) recovers t exactly.

This is an actual source-facing coverage theorem for ALL safe
T-support vertices in all sorted frontiers, not only projected
points introduced syntactically as P_i(z).

It does not assert that deeper out-of-budget ambient roots have
a safe local tail: in the printed-style Q decoding those roots
are mapped to a fallback alphabet constant and need a separate
case in the eventual total simplicity-to-smoothness proof.
-/

namespace DualTree.ForwardInverseConeTails

/-- The uniquely recovered canonical local suffix of a
target above a genuine forward-complete frontier, whenever
the intrinsic rank difference fits the common safe domain. -/
noncomputable def relativeTail {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (frontier target : {t : Node b // t ∈ T})
    (_hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    BoundedNode b (k - (m + 1)) := by
  let s := (ForwardCompleteBijection.inverseAddress
    T hcomplete hnon frontier).1
  let t := (ForwardCompleteBijection.inverseAddress
    T hcomplete hnon target).1
  have hs := ForwardCompleteBijection.inverse_length
    T hcomplete hnon frontier
  have ht := ForwardCompleteBijection.inverse_length
    T hcomplete hnon target
  refine ⟨t.drop s.length, ?_⟩
  change (t.drop s.length).length < k - (m + 1)
  simp only [List.length_drop]
  dsimp only [s, t]
  rw [ht, hs]
  exact hbudget

/-- The recovered suffix has exactly the intrinsic
support-rank difference as its length. -/
theorem relativeTail_length {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (frontier target : {t : Node b // t ∈ T})
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    (relativeTail T hcomplete hnon frontier target hprefix hbudget).1.length =
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 := by
  simp only [relativeTail, List.length_drop]
  rw [ForwardCompleteBijection.inverse_length T hcomplete hnon target,
      ForwardCompleteBijection.inverse_length T hcomplete hnon frontier]

/-- Forward-complete inverse addresses decompose EXACTLY
into the frontier address followed by the recovered tail. -/
theorem relativeTail_address {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (frontier target : {t : Node b // t ∈ T})
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    (ForwardCompleteBijection.inverseAddress T hcomplete hnon target).1 =
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon frontier).1 ++
        (relativeTail T hcomplete hnon
          frontier target hprefix hbudget).1 := by
  have hp : IsPrefix
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon frontier).1
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon target).1 :=
    ForwardCompletePrefixIso.inverseAddress_prefix
      T hcomplete hnon frontier target hprefix
  have htake := CutFrontier.take_length_of_prefix hp
  calc
    (ForwardCompleteBijection.inverseAddress T hcomplete hnon target).1 =
      ((ForwardCompleteBijection.inverseAddress
          T hcomplete hnon target).1).take
        (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon frontier).1.length ++
      ((ForwardCompleteBijection.inverseAddress
          T hcomplete hnon target).1).drop
        (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon frontier).1.length :=
          (List.take_append_drop _ _).symm
    _ = (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon frontier).1 ++
      ((ForwardCompleteBijection.inverseAddress
          T hcomplete hnon target).1).drop
        (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon frontier).1.length := by
          rw [htake]
    _ = (ForwardCompleteBijection.inverseAddress
          T hcomplete hnon frontier).1 ++
      (relativeTail T hcomplete hnon
        frontier target hprefix hbudget).1 := rfl

/-- The corrected inverse-address map is injective on
the actual complete support T. -/
theorem inverseAddress_injective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    Function.Injective
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon) := by
  intro x y heq
  calc
    x = ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon
        (ForwardCompleteBijection.inverseAddress T hcomplete hnon x) :=
      (ForwardCompleteBijection.inverse_right
        T hcomplete hnon x).symm
    _ = ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon
        (ForwardCompleteBijection.inverseAddress T hcomplete hnon y) := by
      rw [heq]
    _ = y := ForwardCompleteBijection.inverse_right
      T hcomplete hnon y

/-- Every SAFE forward-support descendant of a sorted
outside-cut frontier is in the image of the genuine corrected
common cone projection. No printed-order assumptions. -/
theorem projectCommon_reaches_target {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier target : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (hprefix : IsPrefix frontier.1 target.1)
    (hbudget :
      SkewTree.heightAt T target.1 - SkewTree.heightAt T frontier.1 <
        k - (m + 1)) :
    ForwardUniformConeDomains.projectCommon T hcomplete hnon
      cut hcut hm frontier hf
      (relativeTail T hcomplete hnon
        frontier target hprefix hbudget) = target := by
  have hproj :=
    ForwardUniformConeDomains.projectCommon_inverse
      T hcomplete hnon cut hcut hm frontier hf
      (relativeTail T hcomplete hnon
        frontier target hprefix hbudget)
  have hsource :
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon
        (ForwardUniformConeDomains.projectCommon T hcomplete hnon
          cut hcut hm frontier hf
          (relativeTail T hcomplete hnon
            frontier target hprefix hbudget))).1 =
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon target).1 := by
    calc
      _ = (ForwardCompleteBijection.inverseAddress
            T hcomplete hnon frontier).1 ++
          (relativeTail T hcomplete hnon
            frontier target hprefix hbudget).1 := hproj
      _ = (ForwardCompleteBijection.inverseAddress
            T hcomplete hnon target).1 :=
        (relativeTail_address T hcomplete hnon
          frontier target hprefix hbudget).symm
  apply inverseAddress_injective T hcomplete hnon
  exact Subtype.ext hsource

/-- Each fixed frontier projection is injective on
its common shortened local tail domain. -/
theorem projectCommon_injective {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1) :
    Function.Injective
      (ForwardUniformConeDomains.projectCommon T hcomplete hnon
        cut hcut hm frontier hf) := by
  intro x y hxy
  have hsource :
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon
        (ForwardUniformConeDomains.projectCommon T hcomplete hnon
          cut hcut hm frontier hf x)).1 =
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon
        (ForwardUniformConeDomains.projectCommon T hcomplete hnon
          cut hcut hm frontier hf y)).1 :=
    congrArg (fun t : {t : Node b // t ∈ T} =>
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon t).1) hxy
  have hconcat :
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon frontier).1 ++ x.1 =
      (ForwardCompleteBijection.inverseAddress T hcomplete hnon frontier).1 ++ y.1 := by
    calc
      _ = (ForwardCompleteBijection.inverseAddress T hcomplete hnon
          (ForwardUniformConeDomains.projectCommon T hcomplete hnon
            cut hcut hm frontier hf x)).1 :=
        (ForwardUniformConeDomains.projectCommon_inverse
          T hcomplete hnon cut hcut hm frontier hf x).symm
      _ = (ForwardCompleteBijection.inverseAddress T hcomplete hnon
          (ForwardUniformConeDomains.projectCommon T hcomplete hnon
            cut hcut hm frontier hf y)).1 := hsource
      _ = _ := ForwardUniformConeDomains.projectCommon_inverse
        T hcomplete hnon cut hcut hm frontier hf y
  have hval : x.1 = y.1 := by
    have hdrop := congrArg
      (fun z : Node b =>
        z.drop
          (ForwardCompleteBijection.inverseAddress T hcomplete hnon frontier).1.length)
      hconcat
    simpa using hdrop
  exact Subtype.ext hval


/-- If the local selected bullet point precedes a safe local
address z, then its actual projected Q marked support node
precedes the canonical projected target P_i(z). -/
theorem markedProjection_prefix_projectLocal_of_bullet_prefix
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c)
    (j : MixedProduct.BulletIndex (ForwardSourceQTree.kind c))
    (z : BoundedNode b (k - (m + 1)))
    (hlocal : IsPrefix (x.bulletPoint j).1 z.1) :
    IsPrefix (ForwardSourceQTree.markedProjection c x j).1
      (ForwardQActualCoordinateWord.projectLocal c j.1 z).1 := by
  exact ForwardUniformConeDomains.projectCommon_prefix
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
    (x.bulletPoint j) z hlocal

/-- CONTRAPOSITIVE: a projected local Q support point outside
the actual marked cone must have its local tail outside the
selected bullet-point cone. -/
theorem local_outside_of_projected_outside
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c)
    (j : MixedProduct.BulletIndex (ForwardSourceQTree.kind c))
    (z : BoundedNode b (k - (m + 1)))
    (houtside :
      ¬ IsPrefix (ForwardSourceQTree.markedProjection c x j).1
        (ForwardQActualCoordinateWord.projectLocal c j.1 z).1) :
    ¬ IsPrefix (x.bulletPoint j).1 z.1 := by
  intro hlocal
  exact houtside
    (markedProjection_prefix_projectLocal_of_bullet_prefix
      c x j z hlocal)

/-- For ANY safe T-support descendant of the selected frontier,
being outside its real Q marked cone implies that the UNIQUE
recovered local address lies outside the corresponding D2
marked-point cone. This is the precise geometry needed for
Definition 21's Gamma2 observable-letter implication. -/
theorem local_outside_of_safe_target_outside
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c)
    (j : MixedProduct.BulletIndex (ForwardSourceQTree.kind c))
    (t : {u : Node b // u ∈ c.T})
    (hprefix :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 t.1)
    (hbudget :
      SkewTree.heightAt c.T t.1 -
        SkewTree.heightAt c.T
          (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 <
        k - (m + 1))
    (houtside :
      ¬ IsPrefix (ForwardSourceQTree.markedProjection c x j).1 t.1) :
    ¬ IsPrefix (x.bulletPoint j).1
      (relativeTail c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
        t hprefix hbudget).1 := by
  let z : BoundedNode b (k - (m + 1)) :=
    relativeTail c.T c.hcomplete c.hnon
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
      t hprefix hbudget
  have hrecover :
      ForwardQActualCoordinateWord.projectLocal c j.1 z = t :=
    projectCommon_reaches_target c.T c.hcomplete c.hnon
      c.cut c.hcutT c.hm
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
      t (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
      hprefix hbudget
  intro hlocal
  have hp := markedProjection_prefix_projectLocal_of_bullet_prefix
    c x j z hlocal
  rw [hrecover] at hp
  exact houtside hp

end DualTree.ForwardInverseConeTails
