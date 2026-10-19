# Adversarial continuation — extra retained early roots obstruct reverse Q covering

The genuine corrected final support retains ALL complete ambient T roots
up to the inclusive forward cut.  The old source starred word g' has
only its own source-variable roots (the interior of S).

For an extra retained original f-root u which is NOT a variable root of
g', the typed source substitution rho has exactly two possibilities:
(1) rho(u) is a constant; or (2) rho(u) is an old source variable v.
In case (1), every actual fibrewise Q(w) is CONSTANT at u, whereas f'
has an INDEPENDENT root variable at u.  Over a two-letter alphabet an
f' evaluation can disagree with that constant.
In case (2), the source atRoot theorem fixes v at its own original f
root.  Thus the distinct early roots u and v are identified under rho,
so merged PR #382's kernel-checked two-root obstruction applies.

This is a new source-facing theorem: ANY extra retained early f-variable
root outside the g' support implies that some genuine evaluated word in
span(f') is outside ALL evaluated Q(w) outputs, even if w ranges over
the full enlarged mixed-product input domain without W_* restrictions.

Do NOT conclude that such an extra root exists in every frame without
a separate geometric counting or witness argument.  A natural sufficient
condition is retained T-root count > source-variable-root count l; this
requires an independent finite-cardinality proof from the rank m of t0.

Consequence for the manuscript: the current f' construction cannot
justify the proposed full reverse inclusion
  span(f') ⊆ union_w span(Q(w))
whenever retained T has extra variable roots.  The correct forward
inclusion for ANCHORED assignments remains kernel checked.

Potential repair must change the early/root semantics or the
required Ramsey-domain comparison, rather than merely asserting
Q/f' equality for arbitrary early assignments.  The published reverse
auxiliary order and Definition 24 colouring transport remain separate.
