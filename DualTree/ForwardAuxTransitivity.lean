import DualTree.CanonicalForwardAuxIso

/-!
# Transitivity of the corrected length-first forward-lex auxiliary order

The printed-order skew-tree construction uses an auxiliary order
which sorts ambient length first and reverses lexicographic order
within each level. The proposed repair replaces that tie break
consistently by *forward* lexicographic order.

Reflexivity, totality and antisymmetry of this forward order are
already checked in CanonicalForwardAuxIso. To sort actual
minimal outside-cut frontiers (needed for the Definition 20 starred
coordinate order) we also need transitivity. This file proves it
for arbitrary branching numbers and finite ambient words.

These order-theoretic lemmas do not assume a source skew tree or
claim the repaired Lemma 27.
-/

namespace DualTree.ForwardAuxTransitivity

/-- Finite-word forward lexicographic comparison is transitive. -/
theorem finLexLE_trans {b : Nat} :
    ∀ (s t u : Node b),
      FinLexLE s t → FinLexLE t u → FinLexLE s u := by
  intro s
  induction s with
  | nil =>
      intro t u _ _
      simp [FinLexLE, finLexLEB]
  | cons a as ih =>
      intro t u hst htu
      cases t with
      | nil =>
          simp [FinLexLE, finLexLEB] at hst
      | cons c cs =>
          cases u with
          | nil =>
              simp [FinLexLE, finLexLEB] at htu
          | cons d ds =>
              by_cases hac : a = c
              · subst c
                have hst' : FinLexLE as cs := by
                  simpa [FinLexLE, finLexLEB] using hst
                by_cases hcd : a = d
                · subst d
                  have htu' : FinLexLE cs ds := by
                    simpa [FinLexLE, finLexLEB] using htu
                  simpa [FinLexLE, finLexLEB] using
                    ih cs ds hst' htu'
                · have hlt : a < d := by
                    simpa [FinLexLE, finLexLEB, hcd] using htu
                  have hne : a ≠ d := ne_of_lt hlt
                  simp [FinLexLE, finLexLEB, hne, hlt]
              · have haclt : a < c := by
                  simpa [FinLexLE, finLexLEB, hac] using hst
                by_cases hcd : c = d
                · subst d
                  simp [FinLexLE, finLexLEB, hac, haclt]
                · have hcdlt : c < d := by
                    simpa [FinLexLE, finLexLEB, hcd] using htu
                  have had : a < d := lt_trans haclt hcdlt
                  have hne : a ≠ d := ne_of_lt had
                  simp [FinLexLE, finLexLEB, hne, had]

/-- The globally repaired auxiliary comparison is transitive. -/
theorem forwardAux_trans {b : Nat}
    {s t u : Node b}
    (hst : ForwardAux s t) (htu : ForwardAux t u) :
    ForwardAux s u := by
  rcases hst with hst | ⟨heqst, hlexst⟩
  · rcases htu with htu | ⟨heqtu, _⟩
    · exact Or.inl (lt_trans hst htu)
    · exact Or.inl (by omega)
  · rcases htu with htu | ⟨heqtu, hlextu⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨heqst.trans heqtu,
        finLexLE_trans s t u hlexst hlextu⟩

end DualTree.ForwardAuxTransitivity
