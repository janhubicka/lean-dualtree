import DualTree.Lemma27QTreeCount

/-!
# Marked points are leaves in the reconstructed Lemma 27 tree

The node set S_w consists of an old signature base before the cut and
one projected point for each D₂ coordinate, after the cut and in a
pairwise incomparable frontier cone.

We show that none of the new marked points has any strict descendant
in S_w. Thus every new marked point is a genuine leaf, and every
interior vertex of S_w belongs to the old signature base.

This is one direction of the required interior identification.
The converse, that every old original interior remains interior
in S_w, still depends on the complete marker/frontier successor
coverage and has not been silently assumed.
-/

namespace DualTree.Lemma27QTerminal

/-- In a finite list, a node with no strict descendants cannot have
an immediate successor and hence is not interior. -/
theorem not_interior_of_no_strict_descendant {b : Nat}
    (S : List (Node b)) (r : Node b)
    (hno : ∀ s, s ∈ S → ¬ IsStrictPrefix r s) :
    r ∉ SkewTree.interior S := by
  intro hInt
  have h : r ∈ S.filter
      (fun s => !(SkewTree.immediateSuccs S s).isEmpty) := hInt
  have hflag := (List.mem_filter.mp h).2
  cases hsucc : SkewTree.immediateSuccs S r with
  | nil =>
      simp [hsucc] at hflag
  | cons t ts =>
      have ht : t ∈ SkewTree.immediateSuccs S r := by
        simp [hsucc]
      have ht' : t ∈ S.filter
          (fun s => SkewTree.immediateSuccB S r s) := ht
      have htS : t ∈ S := (List.mem_filter.mp ht').1
      have hstep : SkewTree.immediateSuccB S r t = true :=
        (List.mem_filter.mp ht').2
      have hstrict : IsStrictPrefix r t :=
        ((SkewBranchGeometry.immediateSuccB_iff S r t).1 hstep).2.1
      exact hno t htS hstrict

/-- A new marked node has no strict descendant anywhere in the Q
skeleton, provided its fixed old base lies before the cut. -/
theorem markedProjection_no_strict_descendant
    {b k m : Nat}
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
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind)
    (s : Node b)
    (hs : s ∈ Lemma27SignatureTree.signatureNodes
      T hcomplete cut hcut hlevel hm base x) :
    ¬ IsStrictPrefix
      (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcut hlevel hm x i).1 s := by
  classical
  intro hstrict
  unfold Lemma27SignatureTree.signatureNodes at hs
  rcases Finset.mem_union.mp hs with hOld | hNew
  · have hEarly : PaperAux s cut :=
      hbase s (List.mem_toFinset.mp hOld)
    have hmarkEarly : PaperAux
      (Lemma27SignatureTree.markedProjection
        T hcomplete cut hcut hlevel hm x i).1 cut :=
      CutPreservation.paperAux_of_prefix hstrict.1 hEarly
    exact (Lemma27MarkedLeafGeometry.markedProjection_after_cut
      T hcomplete cut hcut hlevel hm x i) hmarkEarly
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hNew
    have hij :=
      Lemma27MarkedLeafGeometry.markedProjection_prefix_implies_same_index
        T hcomplete cut hcut hlevel hm x i j hstrict.1
    subst j
    exact hstrict.2 rfl

/-- Every new D₂ point is a terminal leaf of the actual finite
node set S_w, not merely of its coordinate cone. -/
theorem markedProjection_not_interior
    {b k m : Nat}
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
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind) :
    (Lemma27SignatureTree.markedProjection
      T hcomplete cut hcut hlevel hm x i).1 ∉
    SkewTree.interior
      (Lemma27SignatureTree.signatureNodes
        T hcomplete cut hcut hlevel hm base x).toList := by
  exact not_interior_of_no_strict_descendant
    (Lemma27SignatureTree.signatureNodes
      T hcomplete cut hcut hlevel hm base x).toList
    (Lemma27SignatureTree.markedProjection
      T hcomplete cut hcut hlevel hm x i).1
    (fun s hs =>
      markedProjection_no_strict_descendant
        T hcomplete cut hcut hlevel hm base hbase x i s
        (by simpa only [Finset.mem_toList] using hs))

/-- Therefore an interior vertex of S_w must belong to the fixed
old signature base; no new marked variable root is created. -/
theorem signatureNodes_interior_subset_base
    {b k m : Nat}
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
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (s : Node b)
    (hs : s ∈ SkewTree.interior
      (Lemma27SignatureTree.signatureNodes
        T hcomplete cut hcut hlevel hm base x).toList) :
    s ∈ base := by
  classical
  have hS : s ∈
      (Lemma27SignatureTree.signatureNodes
        T hcomplete cut hcut hlevel hm base x).toList := by
    have ht := hs
    unfold SkewTree.interior at ht
    exact (List.mem_filter.mp ht).1
  have hfin : s ∈ Lemma27SignatureTree.signatureNodes
      T hcomplete cut hcut hlevel hm base x := by
    simpa only [Finset.mem_toList] using hS
  unfold Lemma27SignatureTree.signatureNodes at hfin
  rcases Finset.mem_union.mp hfin with hOld | hNew
  · exact List.mem_toFinset.mp hOld
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hNew
    exact False.elim
      ((markedProjection_not_interior T hcomplete cut hcut hlevel
        hm base hbase x i) hs)

/-- The actual source-specific reconstruction has no interior
nodes other than the original l interior vertices. -/
theorem sourceSignatureNodes_interior_subset_original
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
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b)
    (hs : s ∈ SkewTree.interior
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList) :
    s ∈ SkewTree.interior O.tree := by
  have hOld : s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
    signatureNodes_interior_subset_base T hcomplete cut hcutT hlevel hm
      (Lemma27SignatureTree.oldSignatureBase O cut hout)
      (SignatureInteriorExact.oldSignatureBase_before_cut O cut hmax hout)
      x s hs
  exact (Lemma27QTreeCount.oldBase_mem_iff_original_interior
    O cut hcut hmax hout s).1 hOld

end DualTree.Lemma27QTerminal
