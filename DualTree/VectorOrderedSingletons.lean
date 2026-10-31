import DualTree.VectorOrderedSingletonPair

/-!
# Arbitrary vectors of ordered singleton 1-complete skew supports

For the mixed D₀/D₂ height-one Ramsey construction, all ordinary
coordinate variable roots may lie at one early ray node, while all
marked-variable roots lie at a separate later ray node. More
generally, any FINITE vector of singleton supports whose ambient
root lengths are weakly increasing in coordinate order satisfies
the exact source-facing vector 1-complete-skew predicate.

This theorem handles arbitrary vector widths, not just Fin 2.
It verifies the entire executable vectorCompleteB, including the
same-intrinsic-level cross-coordinate length comparisons. It does
not assert any higher intrinsic height or D₁ leaf condition.
-/

namespace DualTree.VectorSkew

private theorem list_all_true_of_forall
    {α : Type*} (L : List α) (p : α → Bool)
    (h : ∀ x, x ∈ L → p x = true) :
    L.all p = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true]
    constructor
    · exact h x (by simp)
    · apply ih
      intro y hy
      exact h y (by simp [hy])

/-- At the sole intrinsic level of a singleton support, its
only node is at intrinsic level zero. -/
theorem singleton_levelNodes_zero
    {b : Nat} (s : Node b) :
    levelNodes [s] 0 = [s] := by
  simp [levelNodes, SkewTree.heightAt,
    SkewTree.preds, SkewTree.strictPrefixB]

/-- All singleton root supports satisfy the vector same-level
length requirement if their ambient lengths are weakly
monotone in the order of coordinate indices. -/
theorem monotone_singletons_sameLevel_one
    {b d : Nat}
    (s : Fin d → Node b)
    (hlen : ∀ i j : Fin d, i < j →
      (s i).length ≤ (s j).length) :
    sameLevelOrderedB (fun i => [s i]) 1 = true := by
  unfold sameLevelOrderedB
  apply list_all_true_of_forall
  intro i _
  apply list_all_true_of_forall
  intro j _
  by_cases hij : i < j
  · simp [hij, singleton_levelNodes_zero, hlen i j hij]
  · simp [hij]

/-- The genuine FULL vector 1-complete-skew predicate for
any finite family of singleton supports whose root lengths
are weakly increasing in coordinate order. The supports
may be equal, distinct, or incomparable in tree-prefix
order; the definition requires only the ambient length
condition at this intrinsic height. -/
theorem monotone_singletons_vectorComplete_one
    {b d : Nat}
    (aux : Node b → Node b → Bool)
    (s : Fin d → Node b)
    (hlen : ∀ i j : Fin d, i < j →
      (s i).length ≤ (s j).length) :
    vectorCompleteB aux 1 (fun i => [s i]) = true := by
  have hcomp :
      (SkewTree.allFin d).all
        (fun i => SkewTree.completeB aux 1 [s i]) = true := by
    apply list_all_true_of_forall
    intro i _
    exact SkewTree.singleton_complete_oneB aux (s i)
  have hlevel := monotone_singletons_sameLevel_one s hlen
  simp [vectorCompleteB, hcomp, hlevel,
    successiveLevelsSeparatedB]

end DualTree.VectorSkew
