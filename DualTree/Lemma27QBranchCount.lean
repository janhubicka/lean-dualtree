import DualTree.Lemma27QRooted

/-!
# Exact immediate-successor counts in the reconstructed Q support

Boolean `uniqueBranchB S s i` states that the given direction contains
exactly one *immediate* support successor. To derive the number of
immediate successors, it is still necessary to prove that every
immediate successor occupies exactly one direction.

We build an equivalence between the b directions and the finite
set of immediate successors. Surjectivity uses the first ambient
letter of a strict support extension; injectivity uses uniqueness
of the first ambient letter of any ambient word. This avoids
silently identifying distinct directions or forgetting a successor.

The source-facing consequence is the exact `0 or b` branch-count
clause of semi-completeness for the actual Q support. The remaining
skew-tree order clauses are separate.
-/

namespace DualTree.Lemma27QBranchCount

/-- A node cannot occupy two distinct immediate ambient
directions from the same fixed prefix. -/
theorem first_direction_unique {b : Nat}
    (s t : Node b) (i j : Fin b)
    (hi : IsPrefix (s ++ [i]) t)
    (hj : IsPrefix (s ++ [j]) t) : i = j := by
  have hprefix : IsPrefix (s ++ [i]) (s ++ [j]) :=
    CutFrontier.prefix_of_prefix_length_le hi hj (by simp)
  have heq : s ++ [i] = s ++ [j] :=
    CutPreservation.prefix_eq_of_length_eq hprefix (by simp)
  have hdrop := congrArg (fun w : Node b => w.drop s.length) heq
  simpa using hdrop

/-- If every direction at a node has exactly one immediate
successor and the support has no duplicates, then the
immediate-successor list has length exactly b. -/
theorem immediateSuccs_length_eq_of_full_directions
    {b : Nat} (S : List (Node b)) (hnodup : S.Nodup)
    (s : Node b)
    (hfull : ∀ i : Fin b, SkewTree.uniqueBranchB S s i = true) :
    (SkewTree.immediateSuccs S s).length = b := by
  classical
  let I := SkewTree.immediateSuccs S s
  let K : Finset (Node b) := I.toFinset
  have hI_nodup : I.Nodup := by
    change (S.filter (fun t => SkewTree.immediateSuccB S s t)).Nodup
    exact hnodup.filter _
  have hExists : ∀ i : Fin b,
      ∃ t : Node b, t ∈ SkewTree.branchWitnesses S s i := by
    intro i
    have hlen : (SkewTree.branchWitnesses S s i).length = 1 := by
      simpa [SkewTree.uniqueBranchB] using hfull i
    cases hs : SkewTree.branchWitnesses S s i with
    | nil =>
        simp [hs] at hlen
    | cons t ts =>
        exact ⟨t, by simp [hs]⟩
  choose f hf using hExists
  have hFmem (i : Fin b) : f i ∈ K := by
    have hBranch : SkewTree.immediateSuccB S s (f i) = true :=
      ((SkewBranchGeometry.mem_branchWitnesses_iff S s (f i) i).1
        (hf i)).1
    have hS : f i ∈ S :=
      ((SkewBranchGeometry.immediateSuccB_iff S s (f i)).1 hBranch).1
    apply List.mem_toFinset.mpr
    change f i ∈ S.filter (fun t => SkewTree.immediateSuccB S s t)
    exact List.mem_filter.mpr ⟨hS, hBranch⟩
  let F : Fin b → {t : Node b // t ∈ K} :=
    fun i => ⟨f i, hFmem i⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have hijVal : f i = f j := congrArg Subtype.val hij
    have hdi : IsPrefix (s ++ [i]) (f i) :=
      ((SkewBranchGeometry.mem_branchWitnesses_iff S s (f i) i).1
        (hf i)).2
    have hdj : IsPrefix (s ++ [j]) (f i) := by
      rw [hijVal]
      exact
        ((SkewBranchGeometry.mem_branchWitnesses_iff S s (f j) j).1
          (hf j)).2
    exact first_direction_unique s (f i) i j hdi hdj
  have hsurj : Function.Surjective F := by
    intro t
    have htI : t.1 ∈ I := List.mem_toFinset.mp t.2
    have htimm : SkewTree.immediateSuccB S s t.1 = true := by
      change t.1 ∈ S.filter
        (fun u => SkewTree.immediateSuccB S s u) at htI
      exact (List.mem_filter.mp htI).2
    have hstrict : IsStrictPrefix s t.1 :=
      ((SkewBranchGeometry.immediateSuccB_iff S s t.1).1 htimm).2.1
    obtain ⟨i, hdir⟩ :=
      SupportReachability.first_direction_of_strictPrefix hstrict
    have htBranch : t.1 ∈ SkewTree.branchWitnesses S s i :=
      (SkewBranchGeometry.mem_branchWitnesses_iff S s t.1 i).2
        ⟨htimm, hdir⟩
    have hEq : f i = t.1 :=
      SkewBranchGeometry.eq_of_mem_uniqueBranch
        S s i (hfull i) (hf i) htBranch
    exact ⟨i, Subtype.ext hEq⟩
  have hcard : Fintype.card (Fin b) =
      Fintype.card {t : Node b // t ∈ K} :=
    Fintype.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  have hcount : b = K.card := by
    simpa using hcard
  have hlength : I.length = K.card :=
    (List.toFinset_card_of_nodup hI_nodup).symm
  exact hlength.trans hcount.symm

/-- At every node of the actual Q support, the number of
immediate successors is either zero or exactly b. This is
the numerical branching part of semi-completeness, without
making an assertion about the auxiliary order. -/
theorem sourceQ_zero_or_b_immediate_successors
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
    (hs : s ∈ (Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList) :
    (SkewTree.immediateSuccs
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      s).length = 0 ∨
    (SkewTree.immediateSuccs
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      s).length = b := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  by_cases hzero : (SkewTree.immediateSuccs W.toList s).length = 0
  · exact Or.inl hzero
  · right
    have hsInterior : s ∈ SkewTree.interior W.toList := by
      unfold SkewTree.interior
      apply List.mem_filter.mpr
      refine ⟨hs, ?_⟩
      cases heq : SkewTree.immediateSuccs W.toList s with
      | nil =>
          simp [heq] at hzero
      | cons t ts =>
          simp [heq]
    exact immediateSuccs_length_eq_of_full_directions W.toList
      (Finset.nodup_toList W) s
      (fun i =>
        Lemma27QRooted.sourceQ_full_immediate_at_nonleaf
          hb O cut hcut hmax hout T hcomplete hST hcutT hlevel
          hm x s hsInterior i)

end DualTree.Lemma27QBranchCount
