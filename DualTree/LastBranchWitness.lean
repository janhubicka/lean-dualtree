import DualTree.PaperAuxAntisymm

/-!
# A sufficient certificate for skew clause (iv)

The final branching-witness clause needs only a designated support
node cut which has all b directional immediate successors, full
branching at all nodes earlier than cut, and no branching at
nodes later than cut. Choosing the maximal direction b-1 is then
forced by the exact b-way successor count.

This purely Boolean lemma does not assert the independent skew
clauses (ii) and (iii). A later source-facing module will prove
the hypotheses for the actual Q construction.
-/

namespace DualTree.LastBranchWitness

/-- Under positive branching, a full last support witness gives
the paper's executable skew clause (iv). -/
theorem condIVB_of_full_last_witness
    {b : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (S : List (Node b)) (cut : Node b)
    (hcut : cut ∈ S)
    (hfullBefore : SkewTree.fullBeforeB aux S cut = true)
    (hemptyAfter : SkewTree.emptyAfterB aux S cut = true)
    (hcutCount : (SkewTree.immediateSuccs S cut).length = b)
    (hfullCut : ∀ i : Fin b, SkewTree.uniqueBranchB S cut i = true) :
    SkewTree.condIVB aux S = true := by
  let iLast : Fin b := ⟨b - 1, by omega⟩
  have hLast : iLast.val + 1 = b := by
    dsimp [iLast]
    omega
  have hpartial : SkewTree.partialAtB S cut iLast = true := by
    change
      ((SkewTree.immediateSuccs S cut).length == iLast.val + 1 &&
        (SkewTree.dirsUpTo iLast).all
          (fun i => SkewTree.uniqueBranchB S cut i)) = true
    simp only [Bool.and_eq_true]
    constructor
    · simp [hcutCount, hLast]
    · apply List.all_eq_true.mpr
      intro i hi
      exact hfullCut i
  unfold SkewTree.condIVB
  apply List.any_eq_true.mpr
  refine ⟨cut, hcut, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨iLast, DirectionalSupport.mem_allFin b iLast, ?_⟩
  simp [hfullBefore, hemptyAfter, hpartial]

end DualTree.LastBranchWitness
