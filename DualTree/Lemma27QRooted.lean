import DualTree.Lemma27QImmediate

/-!
# Rootedness and full branching of non-leaves in the reconstructed Q tree

Ambient meet-closure plus nonemptiness already gives a common support
root: iteratively take the ambient meets of all listed nodes.
This requires neither prefix closure nor the paper's auxiliary order.

The actual reconstructed Q support contains the distinguished old
interior cut and is meet-closed, so it is rooted. In addition, for
positive branching, its interior agrees exactly with the old source
interior. The source-facing immediate-direction theorem can therefore
be applied to every non-leaf of Q, not only to vertices independently
identified as old interior.

The exact numerical successor count and the remaining skew clauses
are deliberately not claimed here.
-/

namespace DualTree.Lemma27QRooted

/-- A nonempty finite subset closed under ambient pairwise meets
has a member preceding every member in the ambient prefix order. -/
theorem common_support_root_of_meetClosed
    {b : Nat} (S : List (Node b))
    (hmeet : MeetGeometry.MeetClosed S)
    (hex : ∃ x : Node b, x ∈ S) :
    ∃ root : Node b, root ∈ S ∧
      ∀ t : Node b, t ∈ S → IsPrefix root t := by
  have hbuild : ∀ L : List (Node b),
      (∀ t : Node b, t ∈ L → t ∈ S) →
      ∃ root : Node b, root ∈ S ∧
        ∀ t : Node b, t ∈ L → IsPrefix root t := by
    intro L
    induction L with
    | nil =>
        intro _
        obtain ⟨x, hx⟩ := hex
        refine ⟨x, hx, ?_⟩
        intro t ht
        cases ht
    | cons x xs ih =>
        intro hsub
        have hx : x ∈ S := hsub x (by simp)
        have hsubxs : ∀ t : Node b, t ∈ xs → t ∈ S := by
          intro t ht
          exact hsub t (List.mem_cons_of_mem x ht)
        obtain ⟨r, hr, hrpre⟩ := ih hsubxs
        let m := MeetGeometry.commonPrefix x r
        have hm : m ∈ S := hmeet x r hx hr
        refine ⟨m, hm, ?_⟩
        intro t ht
        rcases List.mem_cons.mp ht with htx | htxs
        · subst t
          exact MeetGeometry.commonPrefix_prefix_left x r
        · exact isPrefix_trans
            (MeetGeometry.commonPrefix_prefix_right x r)
            (hrpre t htxs)
  exact hbuild S (fun t ht => ht)

/-- A nonempty meet-closed node support satisfies the executable
rootedness axiom without assuming skewness. -/
theorem rootedB_of_meetClosed_nonempty
    {b : Nat} (S : List (Node b))
    (hmeet : MeetGeometry.MeetClosed S)
    {x : Node b} (hx : x ∈ S) :
    SkewTree.rootedB S = true := by
  obtain ⟨root, hroot, hprefix⟩ :=
    common_support_root_of_meetClosed S hmeet ⟨x, hx⟩
  unfold SkewTree.rootedB
  apply List.any_eq_true.mpr
  refine ⟨root, hroot, ?_⟩
  apply List.all_eq_true.mpr
  intro t ht
  exact SkewBranchGeometry.isPrefixOf_true_of_prefix
    (hprefix t ht)

/-- The actual reconstructed support S_w is rooted, independently
of its as-yet-unchecked auxiliary-order and skew-rank clauses. -/
theorem sourceQ_rooted
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
    SkewTree.rootedB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hcutW : cut ∈ W.toList :=
    Lemma27QInterior.originalInterior_mem_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x cut hcut
  exact rootedB_of_meetClosed_nonempty W.toList
    (Lemma27QMeet.sourceQ_meetClosed
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x)
    hcutW

/-- With positive branching, the original-interior and Q-interior
identification upgrades the immediate-direction theorem to
every *actual non-leaf* of S_w. -/
theorem sourceQ_full_immediate_at_nonleaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
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
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList)
    (i : Fin b) :
    SkewTree.uniqueBranchB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      s i = true := by
  have hsOld : s ∈ SkewTree.interior O.tree :=
    (Lemma27QInterior.source_interior_iff_original
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s).1 hs
  exact Lemma27QImmediate.sourceQ_full_immediate_directions
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
    s hsOld i

end DualTree.Lemma27QRooted
