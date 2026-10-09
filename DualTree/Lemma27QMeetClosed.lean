import DualTree.MeetImageTransfer
import DualTree.Lemma27QPrefixSurjectivity
import DualTree.Lemma27QBranchDirections
import DualTree.MeetClosedDirectionConverse

/-!
# Ambient meet closure of the reconstructed Lemma 27 Q tree

The literal pre-replacement skeleton Int(S′) ∪ {t₀} ∪ R is already
proved meet-closed, with the stronger property that the meet of
any two distinct source nodes belongs to the old interior base.

The Q reconstruction gives a genuine prefix-poset isomorphism of
finite node sets. Although this does not automatically transport
ambient meets, the replacement additionally preserves the first
ambient successor direction from every retained original interior
node to every literal marker.

This is precisely the hypothesis of the abstract
MeetImageTransfer theorem: each old meet is fixed, and an extra
common prefix in the target would force an extra shared first
direction in the source.

We prove that the actual reconstructed S_w is therefore closed
under ambient longest common prefixes. Consequently each old
interior node has at most one immediate S_w-successor per ambient
direction. The *existence* of a descendant in every direction was
already checked independently.

The remaining semi-complete counting step is to turn the
directional-existence result into existence of an *immediate*
successor in each direction, and verify the exact number b.
The separate auxiliary-order and skew rank conditions are also
still open.
-/

namespace DualTree.Lemma27QMeetClosed

/-- The actual Q skeleton is ambient meet-closed, not merely
an abstract prefix-poset isomorphic image of the literal skeleton. -/
theorem sourceSignatureNodes_meetClosed
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    MeetGeometry.MeetClosed
      (Lemma27SignatureTree.sourceSignatureNodes O cut
        hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  let P := Lemma27QPrefixSkeleton.Point O cut hout
  let source : P → Node b :=
    Lemma27QPrefixSkeleton.originalNode O cut hout
  let target : P → Node b :=
    Lemma27QPrefixSkeleton.newNode O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x
  let Base : P → Prop := fun p =>
    ∃ u : {u : Node b //
      u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout},
      p = Sum.inl u
  have hfix : ∀ w, Base w → target w = source w := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    rfl
  have hprefix : ∀ a c : P,
      IsPrefix (target a) (target c) ↔
        IsPrefix (source a) (source c) := by
    intro a c
    exact Lemma27QPrefixSkeleton.newNode_prefix_iff_original
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x a c
  have hdir : ∀ w, Base w → ∀ a (i : Fin b),
      IsPrefix (source w ++ [i]) (target a) ↔
        IsPrefix (source w ++ [i]) (source a) := by
    intro w hw a i
    obtain ⟨u, rfl⟩ := hw
    cases a with
    | inl v => rfl
    | inr s =>
        exact Lemma27QBranchDirections.oldBase_childCone_prefix_iff
          O cut hcut hmax hout T hcomplete hST hcutT hlevel
          hm x u.1 u.2 s i
  have hmeets : ∀ a c : P, a ≠ c →
      ∃ w : P, Base w ∧
        source w = MeetGeometry.commonPrefix (source a) (source c) := by
    intro a c hne
    have hlabels : source a ≠ source c := by
      intro h
      exact hne
        (Lemma27QPrefixSkeleton.originalNode_injective
          O cut hcut hmax hout h)
    have ha : source a ∈ SkewTree.interior O.tree ∨
        source a ∈ LiteralSignatureR.literalR O cut hout := by
      cases a with
      | inl u =>
          exact Or.inl
            ((Lemma27QTreeCount.oldBase_mem_iff_original_interior
              O cut hcut hmax hout u.1).1 u.2)
      | inr s => exact Or.inr s.2
    have hc : source c ∈ SkewTree.interior O.tree ∨
        source c ∈ LiteralSignatureR.literalR O cut hout := by
      cases c with
      | inl u =>
          exact Or.inl
            ((Lemma27QTreeCount.oldBase_mem_iff_original_interior
              O cut hcut hmax hout u.1).1 u.2)
      | inr s => exact Or.inr s.2
    have hmeet :
        MeetGeometry.commonPrefix (source a) (source c) ∈
          SkewTree.interior O.tree :=
      Lemma27LiteralMeet.distinct_literal_skeleton_meet_in_original_interior
        O cut hcut hmax hout (source a) (source c)
        ha hc hlabels
    let u : {u : Node b //
      u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout} :=
      ⟨MeetGeometry.commonPrefix (source a) (source c),
        (Lemma27QTreeCount.oldBase_mem_iff_original_interior
          O cut hcut hmax hout _).2 hmeet⟩
    refine ⟨Sum.inl u, ?_, rfl⟩
    exact ⟨u, rfl⟩
  let W := Lemma27SignatureTree.sourceSignatureNodes O cut
    hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hmem : ∀ p : P, target p ∈ W.toList := by
    intro p
    have h :=
      Lemma27QPrefixSurjectivity.newNode_mem_Q
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x p
    simpa only [Finset.mem_toList] using h
  have hsurj : ∀ v : Node b, v ∈ W.toList →
      ∃ p : P, target p = v := by
    intro v hv
    have hfin : v ∈ W := by
      simpa only [Finset.mem_toList] using hv
    exact Lemma27QPrefixSurjectivity.newNode_surjective_on_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x v hfin
  exact MeetImageTransfer.meetClosed_of_prefix_and_directions
    source target Base hfix hprefix hdir hmeets W.toList hmem hsurj

/-- As a direct consequence, the Q node set has at most one
immediate support successor in each of the b ambient directions. -/
theorem sourceSignatureNodes_atMostOneDirection
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    MeetClosedFromBranching.AtMostOneDirection
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList :=
  MeetClosedDirectionConverse.atMostOneDirection_of_meetClosed _
    (sourceSignatureNodes_meetClosed
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x)

end DualTree.Lemma27QMeetClosed
