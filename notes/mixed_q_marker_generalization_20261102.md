# Verified one-D₀ / arbitrary-q-D₂ and p-D₀/q-D₂ height-one mixed Ramsey existence

**3 November 2026.** The entire p/q height-one extension through merged
PR #505 has now passed the full Lean and source/axiom CI at the reviewed
PR heads. The original p=1/q-arbitrary theorem was merged through #499.
The merged code registers **2,111 distinct source-facing axiom reports**;
that count is not a theorem-completion percentage. The merged-main push
CI is a separate verification step.

## Source-facing statement

For branching b>0, finite original alphabet β with a supplied fallback
letter, finite colours γ, and arbitrary p,q : Nat, the checked theorem
`PlainBlockBulletBlock.exists_good_plainBlockBulletBlock_height_one`
gives a finite ambient height n such that EVERY γ-colouring of the
actual `MixedProduct.Element b n (p+q) β (kind p q)`
has a genuine `MixedProduct.VariableWord b n (p+q) 1 β` which is
Definition-11 `Good`.

The first p coordinates are D₀, the last q are independently marked
D₂; there are no D₁ coordinates and the intrinsic height is k=1.
The result is UNCONDITIONAL—no previous `Good` witness is assumed.
Different D₂ marked-letter tuples MAY give different colours.

## Proof and audit ledger

- #493–499: the initial genuine one-D₀ and arbitrary-q-D₂ theorem,
  including exact full span and nonvacuity
- #500: actual complete-skew geometric word with p early D₀
  roots and q later D₂ roots, satisfying the cross-index ordering
- #501: genuine mixed parameter elements and actual observed letters
- #502: every real mixed-span point is represented by p independently
  evaluated Hales–Jewett coordinate words and q marked letters
- #503: positive finite-parameter VECTOR Hales–Jewett existence,
  giving c-goodness of the true mixed product for every colouring
- #505: conversely, EVERY independent assignment of all p D₀
  substitutions and q marked letters occurs in the actual span;
  exact span equality and nonempty span are now checked

The full mixed span is therefore not a potentially empty or restricted
subset of the parameter family. There is no asserted constancy between
distinct retained q-letter tuples. In particular the Γ₁
residual-record nonconstancy counterexample remains respected.

Draft PR #506 proposes a further exact characterization:
`Good color f` if and only if colours on the actual span factor
uniquely through the observed q-letter tuple. This is explicitly
pending CI and is NOT included in the 2,111 merged report count.

## What remains open

The result does not yet cover interleaved D₀/D₂ coordinates (where
cross-coordinate singleton-root length ordering matters), real D₁
up-leaf sets, intrinsic complete-skew height k>1, relative refinement
of a prescribed source word, the printed quantitative Corollary 22
or the Definition 24/ Lemma 27–28 induction. The published dual-tree
theorem also retains the previously recorded refinement and Q-order
counterexample issues, which require corrected statements.
