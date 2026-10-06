import DualTree.Basic

/-!
# Audit of the auxiliary node order

On p. 7 the paper orders shorter nodes first and, among equal-length nodes,
uses reverse lexicographic order. On p. 8 the canonical isomorphism from a
complete skew tree is required to preserve that order.

The three-node binary example
`{[], [false], [true,false]}` already contradicts preservation: in the
source `[true]` precedes `[false]` under the printed reverse-lex convention,
whereas their images have lengths two and one, so the shorter image comes
first.

We encode only the finite order calculation here. The full skew-tree
definition will be layered on top of this file.
-/

namespace DualTree.OrderAudit

/-- Boolean decision procedure for lexicographic `≤` on binary words. -/
def boolLexLEB : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a = b then boolLexLEB as bs else (!a && b)

/-- Lexicographic `≤` on binary words, with `false < true` and prefixes first. -/
def boolLexLE (s t : List Bool) : Prop :=
  boolLexLEB s t = true

/-- The auxiliary order as printed in the paper: length first, reverse lex on ties. -/
def paperAux (s t : List Bool) : Prop :=
  s.length < t.length ∨
    (s.length = t.length ∧ boolLexLE t s)

/-- Candidate repaired convention: length first, forward lex on ties. -/
def forwardAux (s t : List Bool) : Prop :=
  s.length < t.length ∨
    (s.length = t.length ∧ boolLexLE s t)

theorem source_reverse_comparison :
    paperAux [true] [false] := by
  decide

theorem target_reverse_comparison_fails :
    ¬ paperAux [true, false] [false] := by
  decide

/--
The printed auxiliary order cannot be preserved by the canonical map
`[] ↦ []`, `[false] ↦ [false]`, `[true] ↦ [true,false]`.
-/
theorem canonical_order_counterexample :
    paperAux [true] [false] ∧
      ¬ paperAux [true, false] [false] := by
  decide

/-- The same local comparison is consistent with the forward-lex repair. -/
theorem forward_order_repairs_counterexample :
    forwardAux [false] [true] ∧
      forwardAux [false] [true, false] := by
  decide

end DualTree.OrderAudit
