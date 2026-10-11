import DualTree.ForwardQMarkerRanks
import DualTree.ForwardQRetainedRanks
import DualTree.ForwardFrontierRanks
import DualTree.ForwardQRooted

/-!
# Rank of exceptional source leaves and their Q replacement markers

The intrinsic rank of a newly projected Q leaf is determined by
the number of original interior prefixes of its literal boundary
marker. For an exceptional source leaf t outside the final cut,
its first strict-cut boundary r lies on the root-to-t path.
All original interior vertices precede the cut in the repaired
forward auxiliary order; therefore none can lie strictly after r.
This makes the original-interior prefix masks of r and t equal,
so the projected Q leaf has the *same intrinsic Q rank* as t had
in the source S.

Moreover, every exceptional source leaf is itself a minimal
support frontier beyond the inclusive forward cut of S: every
proper support predecessor of a leaf is interior and therefore
at/before the final cut. The forward frontier rank theorem gives

  h_S(t) = h_S(cut)  OR  h_S(t) = h_S(cut)+1.

Thus Q-replaced exceptional leaves lie in a two-level band around
the final source cut; no assumption about local D₂ point depths
enters that intrinsic-rank calculation.

The different "cut-child" markers require their own rank proof.
Neither this theorem nor the companion terminal band proves the
remaining ambient-length comparisons of Q skew clauses (ii)/(iii).
-/

namespace DualTree.ForwardQExceptionalRanks

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- A genuine exceptional source leaf is terminal and lies
strictly outside the final inclusive forward auxiliary cut.
All its proper source-support predecessors belong to the cut. -/
theorem exceptional_is_source_frontier
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves
      c.source c.cut) :
    CutFrontier.Frontier c.source.tree
      (fun u => ForwardAux u c.cut) t := by
  obtain ⟨htSource, htLeaf, _⟩ :=
    StarredSignature.exceptionalLeaves_spec c.source c.cut t ht
  have hcutS : c.cut ∈ c.source.tree :=
    (List.mem_filter.mp c.hcut).1
  have htNe : t ≠ c.cut := by
    intro heq
    subst t
    exact htLeaf c.hcut
  have hfull := StarredSignature.fullBefore_at_maxInterior
    c.source c.cut c.hcut c.hmax
  have hforward : ForwardAux c.cut t :=
    ForwardCutTerminalOrder.cut_forwardAux_before_terminal
      hb c.source.tree c.cut t hfull htSource htLeaf htNe
  have hout : ¬ ForwardAux t c.cut := by
    intro hreverse
    exact htNe (CanonicalForwardAuxIso.forwardAux_antisymm
      hreverse hforward)
  refine ⟨htSource, hout, ?_⟩
  intro u huS hut
  have huInterior :
      u ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree u t huS htSource hut
  simpa [SkewTree.forwardAuxB] using c.hmax u huInterior

/-- Every exceptional source terminal has intrinsic rank
equal to that of the last interior cut, or one higher. -/
theorem exceptional_source_rank_band
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves
      c.source c.cut) :
    SkewTree.heightAt c.source.tree t =
      SkewTree.heightAt c.source.tree c.cut ∨
    SkewTree.heightAt c.source.tree t =
      SkewTree.heightAt c.source.tree c.cut + 1 := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  exact ForwardFrontierRanks.frontier_rank_band
    c.source.tree hsemi.1 (ForwardQRooted.source_nonsingleton c)
    c.cut t (List.mem_filter.mp c.hcut).1
    (exceptional_is_source_frontier hb c t ht)

/-- An interior source vertex is a proper prefix of the first
exceptional-leaf boundary exactly when it is a proper prefix
of that original terminal leaf. -/
theorem interior_prefix_exceptional_boundary_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    IsStrictPrefix s
      (firstBoundary c.cut t.1 (c.hout t.1 t.2)) ↔
    IsStrictPrefix s t.1 := by
  let r := firstBoundary c.cut t.1 (c.hout t.1 t.2)
  have hrSpec : Boundary c.cut t.1 r :=
    firstBoundary_spec c.cut t.1 (c.hout t.1 t.2)
  have hrBound : ForwardInclusiveFrontier.ForwardCutBoundary c.cut r :=
    ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      c.source c.cut c.hout t.1 t.2
  constructor
  · intro hsr
    exact ⟨isPrefix_trans hsr.1 hrSpec.1, by
      intro heq
      have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hsr
      have hrLen := prefix_length_le hrSpec.1
      rw [← heq] at hrLen
      omega⟩
  · intro hst
    have hsEarly : ForwardAux s c.cut := by
      simpa [SkewTree.forwardAuxB] using c.hmax s hs
    have hlength : s.length < r.length := by
      by_contra hn
      have hle : r.length ≤ s.length := by omega
      have hrs : IsPrefix r s :=
        CutFrontier.prefix_of_prefix_length_le
          hrSpec.1 hst.1 hle
      have hrEarly : ForwardAux r c.cut :=
        ForwardInclusiveFrontier.forwardAux_of_prefix hrs hsEarly
      exact hrBound.1 hrEarly
    have hsr : IsPrefix s r :=
      CutFrontier.prefix_of_prefix_length_le
        hst.1 hrSpec.1 (Nat.le_of_lt hlength)
    exact ⟨hsr, by
      intro heq
      have heqlen := congrArg List.length heq
      omega⟩

/-- The projected corrected Q leaf replacing an exceptional
source leaf has the same intrinsic height in Q as that
source leaf had in S, independent of its local D₂ tail. -/
theorem exceptional_projection_Q_rank_eq_source
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut}) :
    let r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
      ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
        ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout t⟩
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c r)).1 =
    SkewTree.heightAt c.source.tree t.1 := by
  classical
  let r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨firstBoundary c.cut t.1 (c.hout t.1 t.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        c.source c.cut c.hmax c.hout t⟩
  change SkewTree.heightAt (nodes c x).toList
    (markedProjection c x
      (ForwardQMarkerCoverage.bulletForMarker c r)).1 =
    SkewTree.heightAt c.source.tree t.1
  rw [ForwardQMarkerRanks.markedProjection_height_eq_marker_prefix_card
    c x r]
  have hsourceNodup : c.source.tree.Nodup := by
    have hsemi := c.source.semi_complete
    simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
    have hskew := hsemi.1
    simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
    simpa using hskew.1
  have hpredNodup : (SkewTree.preds c.source.tree t.1).Nodup := by
    unfold SkewTree.preds
    exact hsourceNodup.filter _
  have hprefixSet :
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun s => SkewTree.strictPrefixB s r.1 = true) =
      (SkewTree.preds c.source.tree t.1).toFinset := by
    ext s
    simp only [Finset.mem_filter, List.mem_toFinset,
      ImmediateSupportHeight.mem_preds_iff]
    constructor
    · rintro ⟨hsInterior, hsBound⟩
      have hsStrict : IsStrictPrefix s r.1 :=
        (SkewBranchGeometry.strictPrefixB_iff s r.1).1 hsBound
      have hst : IsStrictPrefix s t.1 :=
        (interior_prefix_exceptional_boundary_iff c t s
          hsInterior).1 hsStrict
      exact ⟨(List.mem_filter.mp hsInterior).1, hst⟩
    · rintro ⟨hsSource, hst⟩
      have hsInterior :
          s ∈ SkewTree.interior c.source.tree :=
        SignatureInteriorPersistence.interior_of_strict_descendant
          c.source.tree s t.1 hsSource
          (StarredSignature.exceptionalLeaves_spec
            c.source c.cut t.1 t.2).1 hst
      have hsBound : IsStrictPrefix s r.1 :=
        (interior_prefix_exceptional_boundary_iff c t s
          hsInterior).2 hst
      exact ⟨hsInterior,
        (SkewBranchGeometry.strictPrefixB_iff s r.1).2 hsBound⟩
  calc
    ((SkewTree.interior c.source.tree).toFinset.filter
      (fun s => SkewTree.strictPrefixB s r.1 = true)).card =
        (SkewTree.preds c.source.tree t.1).toFinset.card :=
      congrArg Finset.card hprefixSet
    _ = (SkewTree.preds c.source.tree t.1).length :=
      List.toFinset_card_of_nodup hpredNodup
    _ = SkewTree.heightAt c.source.tree t.1 := rfl

end DualTree.ForwardQExceptionalRanks
