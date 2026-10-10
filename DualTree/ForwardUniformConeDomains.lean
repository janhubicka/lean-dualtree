import DualTree.ForwardCanonicalConeCoordinates
import DualTree.ForwardFrontierRanks

/-!
# One uniformly safe cone height for the repaired Lemma 27 construction

In Lemma 27, all minimal support frontiers beyond an auxiliary cut
are used as roots of a mixed-product family of local word cones.

Under the globally corrected forward auxiliary order the
intrinsic height of any such frontier f satisfies

    h_T(cut) ≤ h_T(f) ≤ h_T(cut) + 1.

The right-hand inequality is essential for typing the canonical
projection: the source address I_T^{-1}(f) followed by local tail z
must satisfy

    |I_T^{-1}(f)| + |z| < k,

where T is a k-complete *forward*-skew support.
Consequently all cones share the safe local tail space

    b^{< (k - (m+1))},    m = h_T(cut).

This module constructs a genuinely typed coercion and projection for
*every* forward-cut frontier. It proves preservation of prefixes,
the exact rank increment and the inverse address equation.
An extra-level variant accommodates tails of the paper's original
height k-m, provided the enclosing complete support has height k+1.

The bounds of the recursive Ramsey construction and the full Q
colouring remain to be checked. These are not addressed by the
local cone domain correction alone.
-/

namespace DualTree.ForwardUniformConeDomains

/-- A uniformly shortened local word tail is admissible after
the inverse address of *any* forward-cut frontier. -/
noncomputable def commonTail {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    ForwardCanonicalConeCoordinates.SourceTail T hcomplete hnon frontier := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hfront :=
    ForwardFrontierRanks.frontier_rank_le_cut_succ
      T hparts.1 hnon cut frontier.1 hcut hf
  have hinverse :=
    ForwardCompleteBijection.inverse_length
      T hcomplete hnon frontier
  refine ⟨z.1, ?_⟩
  have hz : z.1.length < k - (m + 1) := z.2
  omega

/-- The locally shortened word address is not changed by
the dependent coercion into its frontier cone. -/
theorem commonTail_value {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    (commonTail T hcomplete hnon cut hcut hm frontier hf z).1 = z.1 := by
  rfl

/-- The common local mixed-product height has an actual
support-valued projection at every forward-cut frontier. -/
noncomputable def projectCommon {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    {t : Node b // t ∈ T} :=
  ForwardCanonicalConeCoordinates.project T hcomplete hnon frontier
    (commonTail T hcomplete hnon cut hcut hm frontier hf z)

/-- Uniform local projections preserve prefix order on all tails. -/
theorem projectCommon_prefix {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (x y : BoundedNode b (k - (m + 1)))
    (hxy : IsPrefix x.1 y.1) :
    IsPrefix
      (projectCommon T hcomplete hnon cut hcut hm frontier hf x).1
      (projectCommon T hcomplete hnon cut hcut hm frontier hf y).1 := by
  exact ForwardCanonicalConeCoordinates.project_prefix
    T hcomplete hnon frontier
    (commonTail T hcomplete hnon cut hcut hm frontier hf x)
    (commonTail T hcomplete hnon cut hcut hm frontier hf y) hxy

/-- Every common projection lies in the ambient support cone
above its selected forward-cut frontier. -/
theorem projectCommon_cone {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    IsPrefix frontier.1
      (projectCommon T hcomplete hnon cut hcut hm frontier hf z).1 := by
  exact ForwardCanonicalConeCoordinates.project_cone
    T hcomplete hnon frontier
    (commonTail T hcomplete hnon cut hcut hm frontier hf z)

/-- The uniform projection increases the intrinsic ambient
support rank by the chosen local tail length, exactly. -/
theorem projectCommon_height {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    SkewTree.heightAt T
      (projectCommon T hcomplete hnon cut hcut hm frontier hf z).1 =
      SkewTree.heightAt T frontier.1 + z.1.length := by
  simpa only [projectCommon, commonTail_value] using
    (ForwardCanonicalConeCoordinates.project_height
      T hcomplete hnon frontier
      (commonTail T hcomplete hnon cut hcut hm frontier hf z))

/-- The forward canonical inverse of a projected node is
the inverse frontier address followed by the common tail. -/
theorem projectCommon_inverse {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    (ForwardCompleteBijection.inverseAddress T hcomplete hnon
      (projectCommon T hcomplete hnon cut hcut hm frontier hf z)).1 =
      (ForwardCompleteBijection.inverseAddress
        T hcomplete hnon frontier).1 ++ z.1 := by
  simpa only [projectCommon, commonTail_value] using
    (ForwardCanonicalConeCoordinates.inverse_project_tail
      T hcomplete hnon frontier
      (commonTail T hcomplete hnon cut hcut hm frontier hf z))

/-- If one extra complete-support level is constructed, the
original paper's longer local tail height k-m is safe even
at frontiers whose intrinsic rank is m+1. -/
noncomputable def extraLevelTail {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB (k + 1) T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - m)) :
    ForwardCanonicalConeCoordinates.SourceTail T hcomplete hnon frontier := by
  have hdim : k + 1 - (m + 1) = k - m := by omega
  let z' : BoundedNode b ((k + 1) - (m + 1)) :=
    ⟨z.1, by simpa only [hdim] using z.2⟩
  exact commonTail T hcomplete hnon cut hcut hm frontier hf z'

theorem extraLevelTail_value {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB (k + 1) T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {f : Node b // f ∈ T})
    (hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) frontier.1)
    (z : BoundedNode b (k - m)) :
    (extraLevelTail T hcomplete hnon cut hcut hm frontier hf z).1 = z.1 := by
  rfl

end DualTree.ForwardUniformConeDomains
