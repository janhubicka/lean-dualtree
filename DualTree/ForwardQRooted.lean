import DualTree.ForwardQFinalCutOrder
import DualTree.ForwardQMarkerCoverage
import DualTree.CompleteSkewMeet
import DualTree.SupportReachability

/-!
# The genuine corrected Q support retains the source root

The complete ambient support T has its own canonical root, but the
Q node set need not contain that root. Rootedness of Q must be proved
using the root of the *original starred source* S.

Because the distinguished cut is an interior vertex of S, S is
nonsingleton and skew, hence has a root r belonging to its
interior. Every original interior point extends r.

The actual corrected literal signature markers are of two types:
* an exceptional-leaf first boundary, lying on the root-to-leaf path;
* a direct ambient child cut++[i], extending cut and hence r.

Every marker lies outside the inclusive forward cut. This ensures
that an exceptional boundary cannot occur above the source root.
Therefore every marker extends r; the sorted canonical cone
projection extends its designated marker, so every new Q node
extends r as well. Since r is retained, the Boolean `rootedB`
predicate holds on the literal forward Q support.

No printed-order canonical map or preselected ambient-T root is used.
This proves rootedness independently of the still open full branch
and skew ambient-length conditions.
-/

namespace DualTree.ForwardQRooted

open ForwardSourceQTree

/-- The original source has at least two nodes because its
distinguished cut is an actual non-leaf. -/
theorem source_nonsingleton
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    c.source.tree.length ≠ 1 := by
  have hcutMem : c.cut ∈ c.source.tree :=
    (List.mem_filter.mp c.hcut).1
  cases hsucc : SkewTree.immediateSuccs c.source.tree c.cut with
  | nil =>
      have htest := (List.mem_filter.mp c.hcut).2
      simp [hsucc] at htest
  | cons u us =>
      have huMem : u ∈ SkewTree.immediateSuccs c.source.tree c.cut := by
        simp [hsucc]
      have huF : u ∈ c.source.tree.filter
          (fun t => SkewTree.immediateSuccB c.source.tree c.cut t) :=
        huMem
      have huTree : u ∈ c.source.tree :=
        (List.mem_filter.mp huF).1
      have huStep : SkewTree.immediateSuccB c.source.tree c.cut u = true :=
        (List.mem_filter.mp huF).2
      have hne : c.cut ≠ u :=
        ((SkewBranchGeometry.immediateSuccB_iff
          c.source.tree c.cut u).1 huStep).2.1.2
      exact SupportReachability.nonsingleton_of_distinct_members
        c.source.tree hcutMem huTree hne

/-- A nonsingleton starred source has a prefix root. -/
theorem source_has_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    ∃ r : Node b, r ∈ c.source.tree ∧
      ∀ t, t ∈ c.source.tree → IsPrefix r t := by
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hroot : SkewTree.rootedB c.source.tree = true :=
    CompleteSkewMeet.rootedB_of_skew_nonSingleton
      SkewTree.forwardAuxB c.source.tree hparts.1
      (source_nonsingleton c)
  unfold SkewTree.rootedB at hroot
  rcases List.any_eq_true.mp hroot with ⟨r, hr, htest⟩
  refine ⟨r, hr, ?_⟩
  intro t ht
  exact DirectionalSupport.prefix_of_isPrefixOf_true
    ((List.all_eq_true.mp htest) t ht)

/-- The actual source-root label, not the root of the ambient T. -/
noncomputable def sourceRoot
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) : Node b :=
  Classical.choose (source_has_root c)

theorem sourceRoot_mem
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    sourceRoot c ∈ c.source.tree :=
  (Classical.choose_spec (source_has_root c)).1

theorem sourceRoot_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b) (ht : t ∈ c.source.tree) :
    IsPrefix (sourceRoot c) t :=
  (Classical.choose_spec (source_has_root c)).2 t ht

/-- The old source root is an interior node, because
it prefixes the cut which is already known to be interior. -/
theorem sourceRoot_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    sourceRoot c ∈ SkewTree.interior c.source.tree := by
  have hcTree : c.cut ∈ c.source.tree :=
    (List.mem_filter.mp c.hcut).1
  have hrootCut : IsPrefix (sourceRoot c) c.cut :=
    sourceRoot_prefix c c.cut hcTree
  by_cases heq : sourceRoot c = c.cut
  · simpa [heq] using c.hcut
  · exact SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree (sourceRoot c) c.cut
      (sourceRoot_mem c) hcTree ⟨hrootCut, heq⟩

/-- Every corrected literal marker lies below the genuine
source root, not merely the root of the enclosing T. -/
theorem sourceRoot_prefix_literal_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout) :
    IsPrefix (sourceRoot c) r.1 := by
  have hcutTree : c.cut ∈ c.source.tree :=
    (List.mem_filter.mp c.hcut).1
  have hrootCut : IsPrefix (sourceRoot c) c.cut :=
    sourceRoot_prefix c c.cut hcutTree
  have hrOutside : ¬ ForwardAux r.1 c.cut :=
    (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
      c.source c.cut c.hcut c.hmax c.hout r.1 r.2).1
  have hlen : (sourceRoot c).length ≤ r.1.length := by
    have hcutLen : c.cut.length ≤ r.1.length := by
      by_contra hn
      exact hrOutside (Or.inl (by omega))
    have hrootLen := prefix_length_le hrootCut
    omega
  have hr :
      r.1 ∈
        (ForwardStarredSignature.signatureTerminalMarkers
            c.source c.cut c.hout ++
          (SkewTree.allFin b).map (fun i => c.cut ++ [i])).dedup := by
    simpa [ForwardStarredSignature.literalR,
      ForwardLiteralFrontierCoordinates.R] using r.2
  simp only [List.mem_dedup, List.mem_append] at hr
  rcases hr with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        c.source c.cut c.hcut c.hmax c.hout r.1 hterminal
    have htSource : t.1 ∈ c.source.tree :=
      (StarredSignature.exceptionalLeaves_spec
        c.source c.cut t.1 t.2).1
    have hrootLeaf : IsPrefix (sourceRoot c) t.1 :=
      sourceRoot_prefix c t.1 htSource
    have hrLeaf : IsPrefix r.1 t.1 := by
      rw [← ht]
      exact (ForwardSignatureBoundary.firstBoundary_spec
        c.cut t.1 (c.hout t.1 t.2)).1
    exact CutFrontier.prefix_of_prefix_length_le
      hrootLeaf hrLeaf hlen
  · obtain ⟨i, _, hi⟩ := List.mem_map.mp hchild
    rw [← hi]
    exact isPrefix_trans hrootCut ⟨[i], rfl⟩

/-- The retained source root is a prefix of every actual Q
vertex, including each sorted D₂ projected marker node. -/
theorem sourceRoot_prefix_Q
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ nodes c x) :
    IsPrefix (sourceRoot c) s := by
  classical
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hs
  rcases Finset.mem_union.mp hs with hbase | hmarked
  · have hsOld : s ∈ SkewTree.interior c.source.tree :=
      (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).1
        (List.mem_toFinset.mp hbase)
    exact sourceRoot_prefix c s (List.mem_filter.mp hsOld).1
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmarked
    have hsurj :=
      (ForwardSortedMixedProduct.bulletIndex_bijective
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly).2
    obtain ⟨r, hr⟩ := hsurj i
    have hIndex : ForwardQMarkerCoverage.bulletForMarker c r = i :=
      hr
    have hrPrefix : IsPrefix (sourceRoot c)
        (markedProjection c x
          (ForwardQMarkerCoverage.bulletForMarker c r)).1 :=
      isPrefix_trans
        (sourceRoot_prefix_literal_marker c r)
        (ForwardQMarkerCoverage.marker_prefix_projected_point c x r)
    rw [hIndex] at hrPrefix
    rw [← hi]
    exact hrPrefix

/-- The real corrected Q support is rooted at the retained
source root. No extra Q-root hypothesis is required. -/
theorem Q_rootedB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.rootedB (nodes c x).toList = true := by
  have hrQ : sourceRoot c ∈ (nodes c x).toList := by
    apply Finset.mem_toList.mpr
    exact ForwardQFixedBase.originalInterior_mem_Q c x
      (sourceRoot c) (sourceRoot_interior c)
  unfold SkewTree.rootedB
  apply List.any_eq_true.mpr
  refine ⟨sourceRoot c, hrQ, ?_⟩
  apply List.all_eq_true.mpr
  intro s hs
  exact SkewBranchGeometry.isPrefixOf_true_of_prefix
    (sourceRoot_prefix_Q c x s (Finset.mem_toList.mp hs))

end DualTree.ForwardQRooted
