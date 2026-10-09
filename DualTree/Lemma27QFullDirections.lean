import DualTree.Lemma27QBranchOccupancy

/-!
# All ambient successor directions occur at the old interior nodes of Q

The first-direction comparison established in the preceding module
reduces the semi-complete branching question to the literal
pre-replacement skeleton Int(S′) ∪ {t₀} ∪ R.

For any original interior node s≠t₀, fullBeforeB at the maximal
interior cut gives a support descendant in each ambient direction.
Such a descendant is either an old interior node, lies below t₀
(which itself is in the skeleton), or is an exceptional leaf.
In the last case, its first non-early boundary belongs to R and
remains in the same direction as seen from s.

At t₀, every immediate ambient child belongs to literal R.
Consequently, every direction from any original interior node
is occupied in the literal skeleton and in S_w.

This proves existence of all b directions; the exact number of
immediate S_w-successors and the other skew axioms remain open.
-/

namespace DualTree.Lemma27QFullDirections

/-- An exceptional leaf reached along the i-th direction from an
old interior vertex has a literal boundary marker in that direction. -/
theorem exceptional_leaf_marker_in_direction
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ u, u ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB u cut = true)
    (hout : ∀ u, u ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut u)
    (s : Node b) (hs : s ∈ SkewTree.interior O.tree)
    (i : Fin b) (t : Node b)
    (hdir : IsPrefix (s ++ [i]) t)
    (ht : t ∈ StarredSignature.exceptionalLeaves O cut) :
    ∃ r : Node b,
      r ∈ LiteralSignatureR.literalR O cut hout ∧
      IsPrefix (s ++ [i]) r := by
  classical
  let r := SignatureBoundary.firstBoundary cut t (hout t ht)
  have hrt : IsPrefix r t :=
    (SignatureBoundary.firstBoundary_spec cut t (hout t ht)).1
  have hrMarker : r ∈ SignatureMarker.boundaryMarkers O cut hout := by
    unfold SignatureMarker.boundaryMarkers
    apply List.mem_map.mpr
    refine ⟨⟨t, ht⟩, ?_, rfl⟩
    simp
  have hrR : r ∈ LiteralSignatureR.literalR O cut hout :=
    Lemma27QMarkerCoverage.boundaryMarker_mem_literalR
      O cut hcut hmax hout hrMarker
  refine ⟨r, hrR, ?_⟩
  by_cases hlen : (s ++ [i]).length ≤ r.length
  · exact CutFrontier.prefix_of_prefix_length_le hdir hrt hlen
  · have hsT : IsPrefix s t :=
      isPrefix_trans ⟨[i], rfl⟩ hdir
    have hrLen : r.length ≤ s.length := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hrS : IsPrefix r s :=
      CutFrontier.prefix_of_prefix_length_le hrt hsT hrLen
    have hsBefore : PaperAux s cut := by
      simpa [SkewTree.paperAuxB] using hmax s hs
    have hrBefore : PaperAux r cut :=
      CutPreservation.paperAux_of_prefix hrS hsBefore
    exact False.elim
      ((InclusiveSignatureMarkers.boundaryMarker_paperCutBoundary
        O cut hout hrMarker).1 hrBefore)

/-- Every original interior vertex has a literal skeleton descendant
in every one of its b ambient immediate-successor cones. -/
theorem oldSkeleton_all_directions
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ u, u ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB u cut = true)
    (hout : ∀ u, u ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut u)
    (s : Node b) (hs : s ∈ SkewTree.interior O.tree)
    (i : Fin b) :
    Lemma27QBranchOccupancy.Occupied
      (Lemma27QBranchOccupancy.oldSkeleton O cut hout) s i := by
  classical
  by_cases heq : s = cut
  · subst s
    have hc : cut ++ [i] ∈ LiteralSignatureR.literalR O cut hout :=
      Lemma27QMarkerCoverage.child_mem_literalR O cut hout i
    refine ⟨cut ++ [i], ?_, isPrefix_refl _⟩
    unfold Lemma27QBranchOccupancy.oldSkeleton
    exact Finset.mem_union.mpr
      (Or.inr (List.mem_toFinset.mpr hc))
  · have hsT : s ∈ O.tree := by
      unfold SkewTree.interior at hs
      exact (List.mem_filter.mp hs).1
    have hfull :=
      StarredSignature.fullBefore_at_maxInterior O cut hcut hmax
    obtain ⟨t, ht, hdir⟩ :=
      DirectionalSupport.directional_descendants_of_fullBefore
        O.tree SkewTree.paperAuxB s cut hfull hsT
        (hmax s hs) heq i
    by_cases htInt : t ∈ SkewTree.interior O.tree
    · have htBase :
          t ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
        (Lemma27QTreeCount.oldBase_mem_iff_original_interior
          O cut hcut hmax hout t).2 htInt
      refine ⟨t, ?_, hdir⟩
      unfold Lemma27QBranchOccupancy.oldSkeleton
      exact Finset.mem_union.mpr
        (Or.inl (List.mem_toFinset.mpr htBase))
    · by_cases hcutT : IsPrefix cut t
      · have hsPrefixT : IsPrefix s t :=
          isPrefix_trans ⟨[i], rfl⟩ hdir
        have hlen : s.length ≤ cut.length := by
          have hBefore : PaperAux s cut := by
            simpa [SkewTree.paperAuxB] using hmax s hs
          rcases hBefore with hlt | ⟨hlen, _⟩ <;> omega
        have hsCut : IsPrefix s cut :=
          CutFrontier.prefix_of_prefix_length_le hsPrefixT hcutT hlen
        have hstrict : IsStrictPrefix s cut := ⟨hsCut, heq⟩
        have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hstrict
        have hchildLen : (s ++ [i]).length ≤ cut.length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hchildCut : IsPrefix (s ++ [i]) cut :=
          CutFrontier.prefix_of_prefix_length_le hdir hcutT hchildLen
        have hcutBase :
            cut ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
          (Lemma27QTreeCount.oldBase_mem_iff_original_interior
            O cut hcut hmax hout cut).2 hcut
        refine ⟨cut, ?_, hchildCut⟩
        unfold Lemma27QBranchOccupancy.oldSkeleton
        exact Finset.mem_union.mpr
          (Or.inl (List.mem_toFinset.mpr hcutBase))
      · have htExceptional :
            t ∈ StarredSignature.exceptionalLeaves O cut := by
          simp [StarredSignature.exceptionalLeaves, ht, htInt, hcutT]
        obtain ⟨r, hr, hdirR⟩ :=
          exceptional_leaf_marker_in_direction
            O cut hcut hmax hout s hs i t hdir htExceptional
        refine ⟨r, ?_, hdirR⟩
        unfold Lemma27QBranchOccupancy.oldSkeleton
        exact Finset.mem_union.mpr
          (Or.inr (List.mem_toFinset.mpr hr))

/-- Every original interior vertex of the reconstructed Q tree
has an actual node in each ambient successor direction. -/
theorem sourceQ_all_directions
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ u, u ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB u cut = true)
    (hout : ∀ u, u ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut u)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b) (hs : s ∈ SkewTree.interior O.tree)
    (i : Fin b) :
    Lemma27QBranchOccupancy.Occupied
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x) s i := by
  have hsBase :
      s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
    (Lemma27QTreeCount.oldBase_mem_iff_original_interior
      O cut hcut hmax hout s).2 hs
  exact (Lemma27QBranchOccupancy.occupied_iff_under_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
      hm x s hsBase i).2
    (oldSkeleton_all_directions O cut hcut hmax hout s hs i)

end DualTree.Lemma27QFullDirections
