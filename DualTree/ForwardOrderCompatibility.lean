import DualTree.CanonicalSupportPrefixIso
import DualTree.SkewLevelOrder

/-!
# Why the forward-lex auxiliary order is the natural candidate repair

The original auxiliary order sorts by ambient length, then by
*reverse* lexicographic order. The printed skew condition (ii),
however, explicitly requires nondecreasing ambient lengths when
nodes at the same intrinsic height are in *forward* lex order.

Consequently condition (ii) gives a direct monotonicity lemma
for the *forward* auxiliary order, not for the printed order:
a fixed-height lexicographic comparison in any skew support
implies the corresponding forward auxiliary comparison.
Likewise skew condition (iii) handles distinct intrinsic heights.

The elementary cone-lex lemma below is useful for the canonical
support-walk proof: ambient branch directions i<j force the
corresponding output nodes to occur in forward lex order, even
when edges of the skew support are stretched.

These generic statements require no changes to the paper's
source definitions and are independent of the currently
unverified global repaired Lemma 27.
-/

namespace DualTree.ForwardOrderCompatibility

/-- A finite-word prefix precedes the full extension in the
paper's ordinary (forward) lexicographic order. -/
theorem finLexLE_of_prefix {b : Nat}
    {s t : Node b} (h : IsPrefix s t) : FinLexLE s t := by
  rcases h with ⟨w, rfl⟩
  induction s with
  | nil =>
      simp [FinLexLE, finLexLEB]
  | cons a s ih =>
      simpa [FinLexLE, finLexLEB] using ih

/-- Distinct immediate ambient directions preserve ordinary
lex order at their arbitrarily deep descendants. -/
theorem finLexLE_of_ordered_cones {b : Nat}
    (s u v : Node b) (i j : Fin b)
    (hij : i < j)
    (hu : IsPrefix (s ++ [i]) u)
    (hv : IsPrefix (s ++ [j]) v) :
    FinLexLE u v := by
  rcases hu with ⟨x, rfl⟩
  rcases hv with ⟨y, rfl⟩
  induction s with
  | nil =>
      have hne : i ≠ j := ne_of_lt hij
      simp [FinLexLE, finLexLEB, hne, hij]
  | cons a s ih =>
      simpa [FinLexLE, finLexLEB] using ih

/-- Clause (ii) of the skew definition implies monotonicity of
the *forward* auxiliary order across lex-ordered vertices of
equal intrinsic support height.  The printed reverse-lex order
does not have this consequence. -/
theorem forwardAux_of_equal_height_lex
    {b : Nat} (T : List (Node b))
    (hII : SkewTree.condIIB T = true)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hh : SkewTree.heightAt T s = SkewTree.heightAt T t)
    (hlex : FinLexLE s t) : ForwardAux s t := by
  have row := (List.all_eq_true.mp hII) s hs
  have entry := (List.all_eq_true.mp row) t ht
  have hlen : s.length ≤ t.length := by
    simpa [hh, hlex] using entry
  by_cases hlt : s.length < t.length
  · exact Or.inl hlt
  · have heq : s.length = t.length := by omega
    exact Or.inr ⟨heq, hlex⟩

/-- Clause (iii) of the skew definition implies monotonicity
of the forward auxiliary order whenever intrinsic support
height strictly increases. -/
theorem forwardAux_of_lower_height
    {b : Nat} (T : List (Node b))
    (hIII : SkewTree.condIIIB T = true)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (hh : SkewTree.heightAt T s < SkewTree.heightAt T t) :
    ForwardAux s t := by
  have row := (List.all_eq_true.mp hIII) s hs
  have entry := (List.all_eq_true.mp row) t ht
  have hlen : s.length < t.length := by
    simpa [hh] using entry
  exact Or.inl hlen

end DualTree.ForwardOrderCompatibility
