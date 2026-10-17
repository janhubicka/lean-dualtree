import DualTree.ForwardAuxTransitivity

/-!
# Maximal elements of finite sets of forward-ordered tree nodes

The corrected forward auxiliary order is total, reflexive,
transitive and antisymmetric on finite words. Any NONEMPTY finite
list of nodes has an element that dominates every list member in
this order. The proof is constructive at the level of the finite
list except for no choice principle and is independent of tree
branching, skewness or complete-support hypotheses.

This reusable lemma selects the LAST interior branching node
of the genuine rank-filtered final support.
-/

namespace DualTree.ForwardAuxFiniteMaximum

/-- A finite nonempty list has a member maximal in the
forward length-first auxiliary order. -/
theorem exists_maximal {b : Nat}
    (xs : List (Node b)) (hne : xs ≠ []) :
    ∃ t : Node b, t ∈ xs ∧
      ∀ s : Node b, s ∈ xs → ForwardAux s t := by
  induction xs with
  | nil =>
      exact False.elim (hne rfl)
  | cons a tail ih =>
      by_cases htail : tail = []
      · subst tail
        refine ⟨a, by simp, ?_⟩
        intro s hs
        have heq : s = a := by simpa using hs
        subst s
        exact CanonicalForwardAuxIso.forwardAux_refl a
      · obtain ⟨u, hu, hmax⟩ := ih htail
        rcases CanonicalForwardAuxIso.forwardAux_total a u with hau | hua
        · refine ⟨u, by simp [hu], ?_⟩
          intro s hs
          rcases List.mem_cons.mp hs with hsa | htailS
          · subst s
            exact hau
          · exact hmax s htailS
        · refine ⟨a, by simp, ?_⟩
          intro s hs
          rcases List.mem_cons.mp hs with hsa | htailS
          · subst s
            exact CanonicalForwardAuxIso.forwardAux_refl a
          · exact ForwardAuxTransitivity.forwardAux_trans
              (hmax s htailS) hua

end DualTree.ForwardAuxFiniteMaximum
