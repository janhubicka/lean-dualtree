import DualTree.DirectionalSupport

/-!
# Intrinsic height separation in a skew subtree

Clause (iii) of the paper's skew-tree definition says that nodes at
different intrinsic heights are separated in ambient word length. In
particular a node t0 in an earlier intrinsic level precedes the later
branching witness w in both the printed and repaired auxiliary orders.

The remaining step for Lemma 27 is to identify the final branching
witness as lying above intrinsic level m' when m'<m-1.
-/

namespace DualTree.SkewLevelOrder

/-- Clause (iii) follows from skewness for every nonsingleton tree. -/
theorem condIIIB_of_skew
    {b : Nat} (T : List (Node b))
    (aux : Node b → Node b → Bool)
    (hskew : SkewTree.skewB aux T = true)
    (hnonsingleton : T.length ≠ 1) :
    SkewTree.condIIIB T = true := by
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have h := hparts.2
  simp [hnonsingleton, Bool.and_eq_true] at h
  exact h.1.2

/-- Strict increase of intrinsic height forces strict ambient length. -/
theorem length_lt_of_height_lt
    {b : Nat} (T : List (Node b))
    (aux : Node b → Node b → Bool)
    (hskew : SkewTree.skewB aux T = true)
    (hnonsingleton : T.length ≠ 1)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hheight : SkewTree.heightAt T s < SkewTree.heightAt T t) :
    s.length < t.length := by
  have hIII : SkewTree.condIIIB T = true :=
    condIIIB_of_skew T aux hskew hnonsingleton
  have hrow := (List.all_eq_true.mp hIII) s hs
  have hentry := (List.all_eq_true.mp hrow) t ht
  simpa [hheight] using hentry

/-- The printed auxiliary order respects intrinsic height separation. -/
theorem paperAux_of_height_lt
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.paperAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hheight : SkewTree.heightAt T s < SkewTree.heightAt T t) :
    SkewTree.paperAuxB s t = true := by
  have hlen := length_lt_of_height_lt T SkewTree.paperAuxB
    hskew hnonsingleton hs ht hheight
  simp [SkewTree.paperAuxB, PaperAux, hlen]

/-- The same consequence under the forward-lex repair. -/
theorem forwardAux_of_height_lt
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hheight : SkewTree.heightAt T s < SkewTree.heightAt T t) :
    SkewTree.forwardAuxB s t = true := by
  have hlen := length_lt_of_height_lt T SkewTree.forwardAuxB
    hskew hnonsingleton hs ht hheight
  simp [SkewTree.forwardAuxB, ForwardAux, hlen]

end DualTree.SkewLevelOrder
