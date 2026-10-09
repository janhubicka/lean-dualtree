import DualTree.Lemma27QBranchClause

/-!
# Antisymmetry of the printed length-first auxiliary order

The printed order in Section 3 has a separate, verified failure:
the canonical prefix-tree embedding need not preserve it.
The order itself is nonetheless antisymmetric.  Establishing this
fact explicitly will let us verify the last-branching-witness
clause of Lemma 27 without incorrectly assuming that its
reconstructed tree preserves an order isomorphism.
-/

namespace DualTree.PaperAuxAntisymm

/-- Lexicographic weak comparisons in both directions force
equality of finite ambient nodes. -/
theorem finLexLE_antisymm {b : Nat}
    (s t : Node b)
    (hst : FinLexLE s t)
    (hts : FinLexLE t s) : s = t := by
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => rfl
      | cons c cs =>
          simp [FinLexLE, finLexLEB] at hts
  | cons a as ih =>
      cases t with
      | nil =>
          simp [FinLexLE, finLexLEB] at hst
      | cons c cs =>
          by_cases heq : a = c
          · subst c
            have hst' : FinLexLE as cs := by
              simpa [FinLexLE, finLexLEB] using hst
            have hts' : FinLexLE cs as := by
              simpa [FinLexLE, finLexLEB] using hts
            have heqTail : as = cs := ih cs hst' hts'
            simp [heqTail]
          · have hlt : a < c := by
              have htest : decide (a < c) = true := by
                simpa [FinLexLE, finLexLEB, heq] using hst
              simpa using htest
            have hgt : c < a := by
              have htest : decide (c < a) = true := by
                simpa [FinLexLE, finLexLEB, Ne.symm heq] using hts
              simpa using htest
            exact (lt_asymm hlt hgt).elim

/-- Even though canonical tree maps need not preserve PaperAux,
the printed auxiliary comparison is antisymmetric on ambient
nodes, including its reverse-lexicographic tie breaking. -/
theorem paperAux_antisymm {b : Nat}
    {s t : Node b} (hst : PaperAux s t) (hts : PaperAux t s) :
    s = t := by
  rcases hst with hlen | ⟨hlen, hlex⟩
  · rcases hts with hlen' | ⟨hlen', _⟩ <;> omega
  · rcases hts with hlen' | ⟨hlen', hlex'⟩
    · omega
    · exact finLexLE_antisymm s t hlex' hlex

/-- The Boolean wrapper of the printed auxiliary order
is antisymmetric as well. -/
theorem paperAuxB_antisymm {b : Nat} {s t : Node b}
    (hst : SkewTree.paperAuxB s t = true)
    (hts : SkewTree.paperAuxB t s = true) :
    s = t := by
  apply paperAux_antisymm
  · simpa [SkewTree.paperAuxB] using hst
  · simpa [SkewTree.paperAuxB] using hts

end DualTree.PaperAuxAntisymm
