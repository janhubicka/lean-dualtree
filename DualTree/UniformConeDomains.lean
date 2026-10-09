import DualTree.CanonicalConeCoordinates
import DualTree.FrontierHeightBound

/-!
# One common safe tail height for all complete-skew frontier cones

The printed Lemma 27 projects a common product of local words through the
canonical cones of the support. The uncorrected common height may overflow
the canonical source tree at a frontier whose intrinsic height is m+1.

For a k-complete skew support and a cut of intrinsic height m, the
verified frontier bound h_T(t) ≤ m+1 shows that every source tail
z ∈ b^{< (k-(m+1))} fits after every frontier address I_T^{-1}(t).

This file constructs the actual *typed* source-tail coercion uniformly
over all such frontiers, with support-valued projections, rank and
inverse-coordinate equations. It makes no claim that the shortened
common dimension is sufficiently large for the final Hales--Jewett
mixed-product application. That numerical issue is still open.
-/

namespace DualTree.UniformConeDomains

/-- The shortened common tail is a valid local tail for every frontier. -/
noncomputable def commonTail {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    CanonicalConeCoordinates.SourceTail T hcomplete frontier := by
  have hfront : SkewTree.heightAt T frontier.1 ≤ m + 1 :=
    FrontierHeightBound.frontier_height_le_m_succ
      T cut frontier.1 hcomplete hcut hlevel hf hm
  have hinverse :
      (CompleteSupportSurjective.inverseAddress
        T hcomplete frontier).1.length =
      SkewTree.heightAt T frontier.1 :=
    CompleteSupportSurjective.inverse_length T hcomplete frontier
  refine ⟨z.1, ?_⟩
  have hz : z.1.length < k - (m + 1) := z.2
  omega

/-- The typed common tail retains exactly the input local address. -/
theorem commonTail_value {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    (commonTail T hcomplete cut hcut hlevel hm frontier hf z).1 = z.1 := by
  rfl

/-- The uniformly shortened local product has a genuine
support-valued projection in every frontier cone. -/
noncomputable def projectCommon {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    {t : Node b // t ∈ T} :=
  CanonicalConeCoordinates.project T hcomplete frontier
    (commonTail T hcomplete cut hcut hlevel hm frontier hf z)

/-- Uniform cone projections preserve local initial segments. -/
theorem projectCommon_prefix {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (x y : BoundedNode b (k - (m + 1)))
    (hxy : IsPrefix x.1 y.1) :
    IsPrefix
      (projectCommon T hcomplete cut hcut hlevel hm frontier hf x).1
      (projectCommon T hcomplete cut hcut hlevel hm frontier hf y).1 :=
  CanonicalConeCoordinates.project_prefix T hcomplete frontier
    (commonTail T hcomplete cut hcut hlevel hm frontier hf x)
    (commonTail T hcomplete cut hcut hlevel hm frontier hf y) hxy

/-- Every uniform projection lies in its designated support cone. -/
theorem projectCommon_cone {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    IsPrefix frontier.1
      (projectCommon T hcomplete cut hcut hlevel hm frontier hf z).1 :=
  CanonicalConeCoordinates.project_cone T hcomplete frontier
    (commonTail T hcomplete cut hcut hlevel hm frontier hf z)

/-- The intrinsic height of a projected local address advances by its length. -/
theorem projectCommon_height {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    SkewTree.heightAt T
      (projectCommon T hcomplete cut hcut hlevel hm frontier hf z).1 =
      SkewTree.heightAt T frontier.1 + z.1.length := by
  simpa only [projectCommon, commonTail_value] using
    (CanonicalConeCoordinates.project_height T hcomplete frontier
      (commonTail T hcomplete cut hcut hlevel hm frontier hf z))

/-- The canonical inverse recovers exactly the initial frontier
address followed by the original common tail. -/
theorem projectCommon_inverse {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (frontier : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier.1)
    (z : BoundedNode b (k - (m + 1))) :
    (CompleteSupportSurjective.inverseAddress T hcomplete
      (projectCommon T hcomplete cut hcut hlevel hm frontier hf z)).1 =
      (CompleteSupportSurjective.inverseAddress
        T hcomplete frontier).1 ++ z.1 := by
  simpa only [projectCommon, commonTail_value] using
    (CanonicalConeCoordinates.inverse_project_tail T hcomplete frontier
      (commonTail T hcomplete cut hcut hlevel hm frontier hf z))

end DualTree.UniformConeDomains
