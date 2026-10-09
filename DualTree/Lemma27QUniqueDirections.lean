import DualTree.Lemma27QMeetClosed
import DualTree.Lemma27QFullDirections

/-!
# Unique immediate successors in all b directions of the Q tree

The previous results provide the two independent ingredients:
* each original interior node has a Q descendant in every
  ambient first direction;
* the actual reconstructed node set S_w is ambient meet-closed,
  so at most one immediate successor can occur in any direction.

A general finite-list lemma upgrades existence of a directional
descendant to existence of an immediate successor in that direction.
Since a finite set has no repeated vertices and all such successors
must agree, its directional branch-witness list has length exactly one.

Specialising to S_w certifies uniqueBranchB S_w s i for every
original interior node s and every i ∈ Fin b.

Thus the complete *direction-by-direction* branching assertion
required for semi-completeness is now proved, though we still have
to identify the total number of immediate successors with b and
establish the separate skew ordering clauses.
-/

namespace DualTree.Lemma27QUniqueDirections

/-- A duplicate-free list containing an element and no other
distinct element has length exactly one. -/
theorem nodup_length_one_of_unique_member
    {β : Type*} (L : List β) (hnd : L.Nodup)
    (u : β) (hu : u ∈ L)
    (hunique : ∀ v, v ∈ L → v = u) :
    L.length = 1 := by
  cases hL : L with
  | nil =>
      simp [hL] at hu
  | cons v tail =>
      cases tail with
      | nil =>
          simp [hL]
      | cons w rest =>
          have hv : v = u :=
            hunique v (by simp [hL])
          have hw : w = u :=
            hunique w (by simp [hL])
          have hvw : v = w := hv.trans hw.symm
          have hnd' : (v :: w :: rest).Nodup := by
            simpa [hL] using hnd
          have hn : v ∉ w :: rest :=
            (List.nodup_cons.mp hnd').1
          exact False.elim (hn (by simp [hvw]))

/-- In a duplicate-free support with at most one immediate
successor per direction, an existing descendant in that direction
makes the corresponding uniqueBranchB predicate true. -/
theorem uniqueBranchB_of_descendant
    {b : Nat} (S : List (Node b))
    (hnd : S.Nodup)
    (hatmost : MeetClosedFromBranching.AtMostOneDirection S)
    (s : Node b) (hs : s ∈ S)
    (i : Fin b)
    (hdesc : ∃ t, t ∈ S ∧ IsPrefix (s ++ [i]) t) :
    SkewTree.uniqueBranchB S s i = true := by
  obtain ⟨t, ht, hdir⟩ := hdesc
  have hst : IsStrictPrefix s t := by
    refine ⟨isPrefix_trans ⟨[i], rfl⟩ hdir, ?_⟩
    intro heq
    have hlen := prefix_length_le hdir
    simp only [List.length_append, List.length_singleton] at hlen
    rw [← heq] at hlen
    omega
  obtain ⟨u, huS, huImm, hsu, hut⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path S s t ht hst
  have hlen : (s ++ [i]).length ≤ u.length := by
    have hlt :=
      MeetClosedFromBranching.length_lt_of_strictPrefix hsu
    simp only [List.length_append, List.length_singleton]
    omega
  have hdirU : IsPrefix (s ++ [i]) u :=
    CutFrontier.prefix_of_prefix_length_le hdir hut hlen
  have huWitness : u ∈ SkewTree.branchWitnesses S s i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff S s u i).2
      ⟨huImm, hdirU⟩
  have hndB : (SkewTree.branchWitnesses S s i).Nodup := by
    unfold SkewTree.branchWitnesses
    exact hnd.filter _
  have huniq : ∀ v, v ∈ SkewTree.branchWitnesses S s i → v = u := by
    intro v hv
    exact hatmost s hs i v u hv huWitness
  have hlen1 : (SkewTree.branchWitnesses S s i).length = 1 :=
    nodup_length_one_of_unique_member
      (SkewTree.branchWitnesses S s i) hndB u huWitness huniq
  simpa [SkewTree.uniqueBranchB] using hlen1

/-- The actual reconstructed Q support has exactly one immediate
successor in each ambient direction at every original interior node. -/
theorem sourceQ_uniqueBranchB
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
    (s : Node b) (hs : s ∈ SkewTree.interior O.tree)
    (i : Fin b) :
    SkewTree.uniqueBranchB
      (Lemma27SignatureTree.sourceSignatureNodes O cut
        hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      s i = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hnd : W.toList.Nodup := Finset.nodup_toList W
  have hsW : s ∈ W.toList :=
    Lemma27QInterior.originalInterior_mem_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s hs
  have hatmost : MeetClosedFromBranching.AtMostOneDirection W.toList :=
    Lemma27QMeetClosed.sourceSignatureNodes_atMostOneDirection
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  obtain ⟨t, ht, hdir⟩ :=
    Lemma27QFullDirections.sourceQ_all_directions
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s hs i
  have htW : t ∈ W.toList := by
    simpa only [Finset.mem_toList] using ht
  exact uniqueBranchB_of_descendant W.toList hnd hatmost s hsW
    i ⟨t, htW, hdir⟩

end DualTree.Lemma27QUniqueDirections
