import DualTree.Basic

/-!
# General lexicographic and auxiliary orders on tree nodes

This is the source-facing order layer for Section 3.  Both the printed
reverse-lex tie-break and the candidate forward-lex repair are kept explicitly,
so later definitions can state which convention they use.
-/

namespace DualTree

/-- Boolean lexicographic `≤` on lists over `Fin b`, with prefixes first. -/
def finLexLEB {b : Nat} : List (Fin b) → List (Fin b) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, c :: cs =>
      if a = c then finLexLEB as cs else decide (a < c)

/-- Lexicographic `≤` as a proposition. -/
def FinLexLE {b : Nat} (s t : Node b) : Prop :=
  finLexLEB s t = true

instance finLexLE_decidable {b : Nat} (s t : Node b) :
    Decidable (FinLexLE s t) := by
  unfold FinLexLE
  infer_instance

/-- Auxiliary order literally printed on p. 7: length first, reverse lex on ties. -/
def PaperAux {b : Nat} (s t : Node b) : Prop :=
  s.length < t.length ∨
    (s.length = t.length ∧ FinLexLE t s)

instance paperAux_decidable {b : Nat} (s t : Node b) :
    Decidable (PaperAux s t) := by
  unfold PaperAux
  infer_instance

/-- Candidate repaired order: length first, forward lex on ties. -/
def ForwardAux {b : Nat} (s t : Node b) : Prop :=
  s.length < t.length ∨
    (s.length = t.length ∧ FinLexLE s t)

instance forwardAux_decidable {b : Nat} (s t : Node b) :
    Decidable (ForwardAux s t) := by
  unfold ForwardAux
  infer_instance

theorem paperAux_of_length_lt {b : Nat} {s t : Node b}
    (h : s.length < t.length) : PaperAux s t :=
  Or.inl h

theorem forwardAux_of_length_lt {b : Nat} {s t : Node b}
    (h : s.length < t.length) : ForwardAux s t :=
  Or.inl h

theorem paperAux_of_eq_length {b : Nat} {s t : Node b}
    (hlen : s.length = t.length) (hlex : FinLexLE t s) :
    PaperAux s t :=
  Or.inr ⟨hlen, hlex⟩

theorem forwardAux_of_eq_length {b : Nat} {s t : Node b}
    (hlen : s.length = t.length) (hlex : FinLexLE s t) :
    ForwardAux s t :=
  Or.inr ⟨hlen, hlex⟩

/-- Lexicographic comparison of finite nodes is total. -/
theorem finLexLE_total {b : Nat} (s t : Node b) :
    FinLexLE s t ∨ FinLexLE t s := by
  induction s generalizing t with
  | nil =>
      exact Or.inl (by simp [FinLexLE, finLexLEB])
  | cons a as ih =>
      cases t with
      | nil =>
          exact Or.inr (by simp [FinLexLE, finLexLEB])
      | cons c cs =>
          by_cases h : a = c
          · subst c
            rcases ih cs with htail | htail
            · exact Or.inl (by simpa [FinLexLE, finLexLEB] using htail)
            · exact Or.inr (by simpa [FinLexLE, finLexLEB] using htail)
          · rcases lt_trichotomy a c with hlt | heq | hgt
            · exact Or.inl (by simp [FinLexLE, finLexLEB, h, hlt])
            · exact (h heq).elim
            · have hca : c ≠ a := Ne.symm h
              exact Or.inr (by simp [FinLexLE, finLexLEB, hca, hgt])

end DualTree
