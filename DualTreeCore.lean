import DualTree.SmoothRelation
import DualTree.SkewLevelOrder

/-!
# Fast development entry point for dual-tree formalization

Exports the common finite-tree, variable-word, skew-tree and mixed-product
language, including smoothness and the elementary skew-level lemmas.

The full research/validation umbrella is intentionally separate:
`lake build DualTree` checks ALL source modules and counterexample fixtures;
`lake build` only checks this small reusable foundation.
For proof development use `lake build DualTree.ModuleName` to check a focused
module and its transitive dependencies. CI builds both entry points and runs
the complete source-facing transitive-axiom audit.

This is a build-scope optimization, NOT a deletion of unverified claims or
a declaration that Lemma 27 or the full theorem is established.
-/
