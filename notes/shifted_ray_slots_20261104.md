# Exact shifted-ray slot decoder: D₀/D₂ interleavings

**4 November 2026 — proposed and CI-gated, stacked on #508 and #507.**

The geometric root schedule at #507 supplies the uniform ambient
height d*(N+1)+1 and disjoint ray intervals for all coordinates. The
marker word at #508 supplies the source-faithful 1-complete-skew
component with one prescribed independent D₂ variable.

This next module proves a typed inverse for each D₀ coordinate's
flat-word positions. The decoder slotIndex(i,t) succeeds exactly at
the N ray positions of coordinate i and recovers the unique Fin N
slot. The opposite implication identifies the actual bounded node,
not merely its ambient length. The scheduled plain root is its own
r-th slot; every D₂ marker remains fixed independently of r.

**Why this matters:** to transfer finite-parameter vector Hales–Jewett
into an arbitrarily interleaved mixed word, the colouring must be
defined on actual finite mixed-product elements BEFORE the returned
proper flat word selects r. D₂ roots must therefore be predetermined,
while D₀ words occupy coordinate-specific translated ray slots.
These properties stop a false proof by permuting the previously
checked p-before-q construction.

Still missing: the shifted symbol word itself, at-root and below-root
laws, its exact evaluation/span, the mixed-product word and its
positive c-good Ramsey existence. No higher k or D₁ claim is made.
