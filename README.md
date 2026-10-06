# lean-dualtree

Lean 4 validation of Todorcevic--Tyros, *A Dual Ramsey Theorem for Trees* (arXiv:2207.14599v1).

The repository follows the paper statement-by-statement. `audit.tex` records
imprecisions, counterexamples, proposed repairs, and the corresponding Lean
validation status. Repairs are recorded before they are used in the formal
development.

## Current formalization

The first layer contains:

- finite homogeneous-tree nodes and an explicit prefix relation;
- a formal three-node counterexample to preservation of the paper's printed
  auxiliary order;
- the corresponding local forward-lex repair check;
- an abstract overlap lemma isolating the transitivity needed to repair
  Appendix Remark 3(ii).

Current audited endpoints include:

```lean
DualTree.OrderAudit.canonical_order_counterexample
DualTree.OrderAudit.forward_order_repairs_counterexample
DualTree.Insensitivity.constantOn_union_of_overlap
```

## Build and audit

The Lean version, dependency pins, cache setup, and axiom-audit pattern are
copied from `janhubicka/lean-milliken`. CI runs `lake build` and rejects
`sorryAx` or nonstandard axioms in the source-facing audit endpoints.

## Next steps

The next layer will formalize the full skew / complete-skew / semi-complete
definitions, prove the corrected forward-lex structural lemmas, and encode the
finite counterexamples to Remarks 1--2 before moving to variable words and
span/refinement.
