import DualTree.SkewTree

/-!
# Explicit rank/ambient-length obstruction certificates

Skew clauses (ii) and (iii) are Boolean finite list conditions.
To refute them for an actual reconstructed Q support, it is enough
to exhibit a *single pair of members* with the relevant reversal of
intrinsic rank and ambient length.

Unlike the finite regression in QLengthObstruction, these results
apply to arbitrary finite skew-support candidates, including
noncomputably constructed Q trees. They avoid evaluating the whole
finite support and isolate the exact numerical hypotheses to verify.
-/

namespace DualTree.SkewOrderObstruction

/-- A pair of equal intrinsic rank, ordered lexicographically
in the wrong direction by their ambient lengths, refutes the
executable skew clause (ii). -/
theorem condIIB_ne_true_of_rank_tie_length_reversal
    {b : Nat} (S : List (Node b))
    (s t : Node b) (hs : s ∈ S) (ht : t ∈ S)
    (hrank : SkewTree.heightAt S s = SkewTree.heightAt S t)
    (hlex : FinLexLE s t)
    (hlength : t.length < s.length) :
    SkewTree.condIIB S ≠ true := by
  intro hII
  have hrow := (List.all_eq_true.mp hII) s hs
  have hentry := (List.all_eq_true.mp hrow) t ht
  have hle : s.length ≤ t.length := by
    simpa [SkewTree.condIIB, hrank, hlex] using hentry
  omega

/-- The Boolean clause (ii) actually evaluates to false
whenever such a pair exists. -/
theorem condIIB_false_of_rank_tie_length_reversal
    {b : Nat} (S : List (Node b))
    (s t : Node b) (hs : s ∈ S) (ht : t ∈ S)
    (hrank : SkewTree.heightAt S s = SkewTree.heightAt S t)
    (hlex : FinLexLE s t)
    (hlength : t.length < s.length) :
    SkewTree.condIIB S = false := by
  cases h : SkewTree.condIIB S with
  | false => rfl
  | true =>
      exact False.elim
        (condIIB_ne_true_of_rank_tie_length_reversal S s t hs ht
          hrank hlex hlength h)

/-- Strictly increasing intrinsic height without strictly
increasing ambient word length refutes skew clause (iii). -/
theorem condIIIB_false_of_height_reversal
    {b : Nat} (S : List (Node b))
    (s t : Node b) (hs : s ∈ S) (ht : t ∈ S)
    (hrank : SkewTree.heightAt S s < SkewTree.heightAt S t)
    (hlength : t.length ≤ s.length) :
    SkewTree.condIIIB S = false := by
  have hnot : SkewTree.condIIIB S ≠ true := by
    intro hIII
    have hrow := (List.all_eq_true.mp hIII) s hs
    have hentry := (List.all_eq_true.mp hrow) t ht
    have hlt : s.length < t.length := by
      simpa [SkewTree.condIIIB, hrank] using hentry
    omega
  cases h : SkewTree.condIIIB S with
  | false => rfl
  | true => exact False.elim (hnot h)

/-- For a nonsingleton finite support, failure of clause
(ii) alone refutes the full skew predicate, regardless of
its other branching or rootedness properties. -/
theorem skewB_false_of_condIIB_false
    {b : Nat} (aux : Node b → Node b → Bool)
    (S : List (Node b))
    (hnonsingleton : S.length ≠ 1)
    (hII : SkewTree.condIIB S = false) :
    SkewTree.skewB aux S = false := by
  simp [SkewTree.skewB, hnonsingleton, hII]

/-- The same obstruction makes the entire semi-complete
skew predicate false. -/
theorem semiCompleteB_false_of_condIIB_false
    {b : Nat} (aux : Node b → Node b → Bool)
    (S : List (Node b))
    (hnonsingleton : S.length ≠ 1)
    (hII : SkewTree.condIIB S = false) :
    SkewTree.semiCompleteB aux S = false := by
  have hskew : SkewTree.skewB aux S = false :=
    skewB_false_of_condIIB_false aux S hnonsingleton hII
  simp [SkewTree.semiCompleteB, hskew]

end DualTree.SkewOrderObstruction
