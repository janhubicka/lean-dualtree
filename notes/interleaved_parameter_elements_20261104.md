# Genuine interleaved mixed-product parameter elements

**4 November 2026 — proposed, not yet Lean-verified.**

The arbitrary-coordinate-kind mixed KVariableWord assembled in
#512 needs an exact mixed-span representation before the finite
flat parameter-Hales–Jewett theorem (#511) can produce genuine
Definition-11 c-goodness.

This module defines ACTUAL MixedProduct.Element data indexed by the
original kind : Fin d → CoordKind with NoUp. Each ordinary coordinate
is an independently embedded flat word in its own shifted slots.
Each D₂ coordinate is a genuine FixedRootMarkerWord.valueWord with
an independent marked letter and fixed bounded marker node. Both
the parameter element and its observable marker tuple are defined
BEFORE any choice of Hales–Jewett word or its first variable root.

Source-facing facts: exact D₀ word recovery; D₂ bullet-point
identity; exact recovery of each observed D₂ letter and the whole
marker tuple; fixed D₂ points in EVERY true mixed-span element.
This does not claim colour canonicity or converse span membership.

Further steps: extract independent D₀ variable assignments from
the actual mixed span, then prove positive unconditional c-goodness
using the uniform flat theorem, followed by converse-span
nonvacuity and final record-factorization checks.
