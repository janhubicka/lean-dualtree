import DualTree.Lemma27QMeet
import DualTree.Lemma27QFullDirections
import DualTree.Lemma27QInterior

/-!
# From occupied ambient directions to actual unique support successors

An occupied ambient cone only promises a support descendant.  To
obtain a unique *immediate* successor, take the first support point
on a path to such a descendant.  Because that point is a strict
extension of the parent, its first ambient letter agrees with the
original descendant's first letter.  Ambient meet-closure forbids
two different immediate successors in the same cone.  A duplicate-
free finite list then has exactly one branch witness in that cone.

Applied to the actual Q skeleton, this converts the all-directions
lemma and the newly proved meet-closure into all Boolean
uniqueBranchB clauses at the original interior vertices.

This is a branch-geometry theorem only: no unproved assertion
about the printed auxiliary order, rank, skewness or g_w is made.
-/

namespace DualTree.Lemma27QImmediate

/-- For a duplicate-free support with at most one immediate
successor per direction, any occupied cone has exactly one
immediate support successor in that direction. -/
theorem uniqueBranch_of_directional_descendant
    {b : Nat} (S : List (Node b))
    (hnodup : S.Nodup)
    (hunique : MeetClosedFromBranching.AtMostOneDirection S)
    (s : Node b) (hs : s ∈ S) (i : Fin b)
    (t : Node b) (ht : t ∈ S)
    (hdir : IsPrefix (s ++ [i]) t) :
    SkewTree.uniqueBranchB S s i = true := by
  have hst : IsStrictPrefix s t := by
    refine ⟨isPrefix_trans ⟨[i], rfl⟩ hdir, ?_⟩
    intro heq
    have hlength := prefix_length_le hdir
    have hEqLen := congrArg List.length heq
    simp only [List.length_append, List.length_singleton] at hlength
    omega
  obtain ⟨u, hu, himm, hsu, hut⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path
      S s t ht hst
  have hlen : (s ++ [i]).length ≤ u.length := by
    have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hsu
    simp only [List.length_append, List.length_singleton]
    omega
  have hdirU : IsPrefix (s ++ [i]) u :=
    CutFrontier.prefix_of_prefix_length_le hdir hut hlen
  have huBranch : u ∈ SkewTree.branchWitnesses S s i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff S s u i).2
      ⟨himm, hdirU⟩
  have hndBranch : (SkewTree.branchWitnesses S s i).Nodup := by
    unfold SkewTree.branchWitnesses
    exact hnodup.filter _
  cases hbr : SkewTree.branchWitnesses S s i with
  | nil =>
      simp [hbr] at huBranch
  | cons v rest =>
      cases rest with
      | nil =>
          simp [SkewTree.uniqueBranchB, hbr]
      | cons w ws =>
          have hv : v ∈ SkewTree.branchWitnesses S s i := by
            simp [hbr]
          have hw : w ∈ SkewTree.branchWitnesses S s i := by
            simp [hbr]
          have hvw : v = w := hunique s hs i v w hv hw
          have hnd : (v :: w :: ws).Nodup := by
            simpa [hbr] using hndBranch
          have hnot : v ∉ w :: ws := (List.nodup_cons.mp hnd).1
          exact False.elim (hnot (by simp [hvw]))

/-- For the *actual* Q support, each of the b ambient cones of
each old interior vertex has exactly one immediate support
successor. This strengthens existence of occupied cones. -/
theorem sourceQ_full_immediate_directions
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
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      s i = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  obtain ⟨t, ht, hdir⟩ :=
    Lemma27QFullDirections.sourceQ_all_directions
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s hs i
  have hsW : s ∈ W.toList :=
    Lemma27QInterior.originalInterior_mem_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s hs
  have htW : t ∈ W.toList := Finset.mem_toList.mpr ht
  exact uniqueBranch_of_directional_descendant
    W.toList (Finset.nodup_toList W)
    (Lemma27QMeet.sourceQ_atMostOneDirection
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x)
    s hsW i t htW hdir

end DualTree.Lemma27QImmediate
