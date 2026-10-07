import DualTree.Basic

/-!
# Theorem 13 final-gluing domain audit

On p. 24 the final definition of the glued words quantifies the tail variable
over b^(n-M) in clauses (ii)--(iv), while the resulting word is defined on
b^{<n}.  If the prefix s_y is at level M, an exact-length (n-M) tail produces
a node of length n and is outside the domain.  The intended tail space is
b^{<n-M}.

The two lemmas below isolate this off-by-one/type error independently of the
rest of the mixed-product construction.
-/

namespace DualTree.GluingAudit

theorem short_tail_stays_in_hom_tree {b M n : Nat}
    (s t : Node b)
    (hM : s.length = M)
    (hMn : M ≤ n)
    (ht : t.length < n - M) :
    InHomTree n (s ++ t) := by
  unfold InHomTree
  simp [List.length_append, hM]
  omega

theorem exact_tail_leaves_hom_tree {b M n : Nat}
    (s t : Node b)
    (hM : s.length = M)
    (hMn : M ≤ n)
    (ht : t.length = n - M) :
    ¬ InHomTree n (s ++ t) := by
  unfold InHomTree
  simp [List.length_append, hM, ht]
  omega

end DualTree.GluingAudit
