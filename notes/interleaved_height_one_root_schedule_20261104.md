# Arbitrary D₀/D₂ interleavings: why a new root schedule is needed

**4 November 2026 — geometry step, CI pending.**

The merged p-D₀/q-D₂ height-one Ramsey construction uses the exact
coordinate order: p ordinary roots all at the earlier first-variable ray
height r, followed by q independently marked roots at the fixed later
height N. Simply permuting this construction for D₂/D₀ interleavings is
not sound: the source-facing vector-complete-skew Boolean predicate
compares ambient root lengths across the ACTUAL coordinate index order.
An early D₂ coordinate with a later D₀ coordinate can violate it.

A candidate repair reserves disjoint ray intervals of length N+1,
one per coordinate i. Set offset(i)=i*(N+1). For the Hales–Jewett
first variable position r< N, choose:
- D₀ root at offset(i)+r; its flat N slots occupy the same interval;
- D₂ root at offset(i), fixed independently of the unknown r.

Then for every i<j,
  rootLength(i)<(i+1)*(N+1)≤j*(N+1)≤rootLength(j),
and all nodes fit in b^{<d*(N+1)+1}. The corresponding singleton
supports satisfy the FULL executable vector height-one predicate.
The results are valid for arbitrary ordered kind patterns, but do
not fill D₁ up-leaf data.

**Scope warning:** This is geometry only, not positive mixed Ramsey
existence. The next needed Lean construction is a shifted-ray
KVariableWord per D₀ block, a fixed-root singleton word per D₂ block,
and genuine componentwise evaluation/span transport. Only then can
parameter-vector Hales–Jewett yield c-goodness in arbitrary coordinate
order. The general k>1 and D₁ cases remain open.

No theorem-level finality or percentage is inferred from the number
of registered axiom reports.
