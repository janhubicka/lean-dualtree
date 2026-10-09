import DualTree.Lemma27SignatureTree
import Mathlib.Data.Finset.Card

/-!
# Geometry of the new marked leaves in Lemma 27's Q tree

The printed S_w adjoins P_i(s_i) in the pairwise disjoint cones
above the minimal support frontiers t_i. The previous module
proved only injectivity of the map i ↦ P_i(s_i).

This module proves the stronger facts needed in the later
semi-complete-tree check:
* no newly marked node is at or before the auxiliary cut t₀;
* two distinct newly marked nodes cannot be prefix-comparable;
* if the old signature base is entirely at or before the cut, it
  is disjoint from all added nodes, and the size of S_w is
  exactly |base| + |D₂|.

The last cardinality formula is explicitly conditional on the
old-base order claim, which has not yet been derived for the
actual Int(S') ∪ {t₀}.
-/

namespace DualTree.Lemma27MarkedLeafGeometry

/-- Every projected new marker is strictly after the inclusive
auxiliary cut, since its minimal support frontier is outside it. -/
theorem markedProjection_after_cut {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind) :
    ¬ PaperAux
      (Lemma27SignatureTree.markedProjection T hcomplete cut hcut hlevel hm x i).1
      cut := by
  intro hbefore
  have hfi := Lemma27SignatureTree.frontierAt_spec T cut i.1
  have hprefix := Lemma27SignatureTree.markedProjection_frontier_prefix
    T hcomplete cut hcut hlevel hm x i
  have hfrontBefore : PaperAux (Lemma27SignatureTree.frontierAt T cut i.1).1 cut :=
    CutPreservation.paperAux_of_prefix hprefix hbefore
  exact hfi.2.1 hfrontBefore

/-- The new marked points from distinct frontier coordinates are
not even comparable in the ambient prefix order. -/
theorem markedProjection_prefix_implies_same_index {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i j : MixedProduct.BulletIndex kind)
    (hp : IsPrefix
      (Lemma27SignatureTree.markedProjection T hcomplete cut hcut hlevel hm x i).1
      (Lemma27SignatureTree.markedProjection T hcomplete cut hcut hlevel hm x j).1) :
    i = j := by
  have hfi := Lemma27SignatureTree.frontierAt_spec T cut i.1
  have hfj := Lemma27SignatureTree.frontierAt_spec T cut j.1
  have hiprefix : IsPrefix
      (Lemma27SignatureTree.frontierAt T cut i.1).1
      (Lemma27SignatureTree.markedProjection T hcomplete cut hcut hlevel hm x j).1 :=
    isPrefix_trans
      (Lemma27SignatureTree.markedProjection_frontier_prefix
        T hcomplete cut hcut hlevel hm x i) hp
  have hjprefix := Lemma27SignatureTree.markedProjection_frontier_prefix
    T hcomplete cut hcut hlevel hm x j
  have hfront :
      (Lemma27SignatureTree.frontierAt T cut i.1).1 =
      (Lemma27SignatureTree.frontierAt T cut j.1).1 :=
    CutFrontier.frontier_unique_above T (fun t => PaperAux t cut)
      hfi hfj hiprefix hjprefix
  let F := LiteralFrontierCount.frontiers T cut
  have hget : F.get i.1 = F.get j.1 := by
    simpa [F, Lemma27SignatureTree.frontierAt] using hfront
  have hequiv :
      (List.Nodup.getEquiv F (LiteralFrontierCount.frontiers_nodup T cut)) i.1 =
      (List.Nodup.getEquiv F (LiteralFrontierCount.frontiers_nodup T cut)) j.1 :=
    Subtype.ext hget
  have hij : i.1 = j.1 :=
    (List.Nodup.getEquiv F
      (LiteralFrontierCount.frontiers_nodup T cut)).injective hequiv
  exact Subtype.ext hij

/-- If every old base vertex is at or before the cut, then none
of the new markers can collide with it. In that case the
reconstructed node set has the expected cardinality. -/
theorem signatureNodes_card_of_base_early {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (base : List (Node b))
    (hbase : ∀ s, s ∈ base → PaperAux s cut)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind) :
    (Lemma27SignatureTree.signatureNodes
        T hcomplete cut hcut hlevel hm base x).card =
      base.toFinset.card + Fintype.card (MixedProduct.BulletIndex kind) := by
  classical
  let M : Finset (Node b) :=
    (Finset.univ : Finset (MixedProduct.BulletIndex kind)).image
      (fun i => (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcut hlevel hm x i).1)
  have hdisj : Disjoint base.toFinset M := by
    apply Finset.disjoint_left.mpr
    intro s hs hM
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hM
    exact (markedProjection_after_cut T hcomplete cut hcut hlevel hm x i)
      (hbase _ (List.mem_toFinset.mp hs))
  have hinjective : Function.Injective
      (fun i : MixedProduct.BulletIndex kind =>
        (Lemma27SignatureTree.markedProjection
          T hcomplete cut hcut hlevel hm x i).1) := by
    intro i j hij
    exact Lemma27SignatureTree.markedProjection_injective
      T hcomplete cut hcut hlevel hm x (Subtype.ext hij)
  have hcard : M.card = Fintype.card (MixedProduct.BulletIndex kind) := by
    change ((Finset.univ : Finset (MixedProduct.BulletIndex kind)).image
      (fun i => (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcut hlevel hm x i).1)).card =
      Fintype.card (MixedProduct.BulletIndex kind)
    rw [Finset.card_image_iff.mpr
      (fun i _ j _ hij => hinjective hij)]
    simp
  change (base.toFinset ∪ M).card =
    base.toFinset.card + Fintype.card (MixedProduct.BulletIndex kind)
  rw [Finset.card_union_of_disjoint hdisj, hcard]

end DualTree.Lemma27MarkedLeafGeometry
