import DualTree.MeetImageTransfer
import DualTree.Lemma27QPrefixSurjectivity
import DualTree.MeetClosedDirectionConverse

/-!
# Ambient meet-closure of the actual reconstructed Lemma 27 Q support

This instantiates the generic direction-preserving meet transport with
the **literal** old signature skeleton and the actual reconstructed
finite node set S_w.  The occurrence type distinguishes old interior
nodes from literal R markers.  Its original labels are distinct and
every meet of two distinct labels belongs to the fixed old interior.

The Q leaf replacement fixes each old interior node, preserves and
reflects ambient prefix relations on all occurrences, and preserves
every immediate ambient cone seen from a fixed old interior node.
Moreover, every Q node has a representing occurrence.  The abstract
meet-transport theorem therefore gives actual ambient meet-closure of
S_w; the general converse then rules out two immediate successors
occupying the same direction.

No claim is made here about the auxiliary order, the node rank
bounds, skewness, the word component g_w, or smoothness.
-/

namespace DualTree.Lemma27QMeet

/-- The actual reconstructed Q node set is closed under longest
common ambient prefixes.  In contrast to a mere prefix-poset
isomorphism, this uses the verified preservation of every direction
from the fixed old interior. -/
theorem sourceQ_meetClosed
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
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  let P := Lemma27QPrefixSkeleton.Point O cut hout
  let source : P → Node b :=
    Lemma27QPrefixSkeleton.originalNode O cut hout
  let target : P → Node b :=
    Lemma27QPrefixSkeleton.newNode
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  let Base : P → Prop := fun p =>
    ∃ u : {u : Node b //
        u ∈ Lemma27SignatureTree.oldSignatureBase O cut hout},
      p = Sum.inl u
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x

  have hfix : ∀ p, Base p → target p = source p := by
    intro p hp
    obtain ⟨u, rfl⟩ := hp
    rfl

  have hprefix : ∀ a c,
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
    | inl v => exact Iff.rfl
    | inr s =>
        exact Lemma27QBranchDirections.oldBase_childCone_prefix_iff
          O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
          x u.1 u.2 s i

  have hmeets : ∀ a c, a ≠ c →
      ∃ w, Base w ∧
        source w = MeetGeometry.commonPrefix (source a) (source c) := by
    intro a c hne
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
    have hneLabels : source a ≠ source c := by
      intro hEq
      exact hne
        (Lemma27QPrefixSkeleton.originalNode_injective
          O cut hcut hmax hout hEq)
    let meet := MeetGeometry.commonPrefix (source a) (source c)
    have hm : meet ∈ SkewTree.interior O.tree :=
      Lemma27LiteralMeet.distinct_literal_skeleton_meet_in_original_interior
        O cut hcut hmax hout (source a) (source c) ha hc hneLabels
    have hmBase :
        meet ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
      (Lemma27QTreeCount.oldBase_mem_iff_original_interior
        O cut hcut hmax hout meet).2 hm
    refine ⟨Sum.inl ⟨meet, hmBase⟩, ?_, ?_⟩
    · exact ⟨⟨meet, hmBase⟩, rfl⟩
    · rfl

  have hmem : ∀ p : P, target p ∈ W.toList := by
    intro p
    exact Finset.mem_toList.mpr
      (Lemma27QPrefixSurjectivity.newNode_mem_Q
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x p)

  have hsurj : ∀ v, v ∈ W.toList → ∃ p : P, target p = v := by
    intro v hv
    exact Lemma27QPrefixSurjectivity.newNode_surjective_on_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
      v (Finset.mem_toList.mp hv)

  exact MeetImageTransfer.meetClosed_of_prefix_and_directions
    source target Base hfix hprefix hdir hmeets W.toList hmem hsurj

/-- Each direction below a Q node contains at most one *immediate*
Q successor: a consequence of ambient meet-closure, not merely
of the existence of descendants in every direction. -/
theorem sourceQ_atMostOneDirection
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
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  exact MeetClosedDirectionConverse.atMostOneDirection_of_meetClosed
    _ (sourceQ_meetClosed O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x)

end DualTree.Lemma27QMeet
