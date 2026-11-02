# Verified one-D₀ / arbitrary-q-D₂ mixed Ramsey existence, and the next geometry

**2 November 2026.** The source-faithful q-marker c-good theorem is
merged and Lean-verified through PR #499. The full converse
exact-span coverage and nonvacuity check also passed full CI. The genuinely new
multiple-D₀ generalization is being developed in stacked PRs #500–503
and is not marked verified here.

## What is unconditional and kernel checked

For a branching factor `b > 0`, a finite original alphabet `β`
with an explicitly supplied fallback letter, a finite colour type
`γ`, and **any** number `q : Nat` of marked coordinates, the
theorem

`DualTree.PlainBulletBlock.exists_good_plainBulletBlock_height_one`

supplies a finite ambient height `n` such that **every** colouring
of the actual `MixedProduct.Element b n (q+1) β (kind q)` admits
a genuine `MixedProduct.VariableWord b n (q+1) 1 β` with
Definition-11 `MixedProduct.Good`. The coordinate-kind pattern is
one `D₀` coordinate followed by `q` independent `D₂`
coordinates; `D₁` is genuinely empty.

This is not an assumption `hgood` passed to a conditional
colour-transfer theorem. It is an existence result obtained from
Mathlib's finite multidimensional Hales–Jewett theorem via its
verified finite-parameter version, using parameter space
`Fin q → β` and original colour type `γ`.

## Why independently marked coordinates are essential

The `D₀` word's true variable root is the first variable
occurrence on an initial homogeneous-tree ray segment.
Its variable positions are all before ray level `N`.
Every `D₂` component has an independent word-variable name
at a *later* ray root of length `N`, and is constant away
from its own root. The geometric marker node may be the same
in different `D₂` components, but their evaluation functions
are independent. The full vector 1-complete-skew predicate,
including the cross-coordinate length-order clause, is checked
rather than assumed.

The actual mixed span has an independently assigned ordinary
Hales–Jewett variable and a tuple of `q` marked letters.
The source-facing span representation is proved in #496.
Equality of Definition-11 observed marked letters identifies
the parameter tuple, so the Hales–Jewett conclusion gives equal
colours for the ordinary-word substitutions. It does NOT assert
equality of colours for different marked-letter tuples.

## Audit trail and the nonvacuity check

- #493: uniform finite-parameter **vector** Hales–Jewett input
  (independent D₀ assignments and arbitrary finite D₂ tuple).
- #494: full ordered-singleton vector 1-complete-skew geometry
  for arbitrary vector width.
- #495: one-D₀ / q-D₂ genuine mixed variable-word support.
- #496: every actual mixed-span element is represented by the
  Hales–Jewett word and a q-tuple of observed letters.
- #498: unconditional Definition-11 c-good existence for every q,
  subsuming the q=1 theorem #490.
- #499: **verified** converse, asserting that every pair of D₀
  assignment and D₂ letter tuple is actually realized, with
  exact equality of the mixed span and parameter family.

Merged #499 brings the library to **2,087** registered source-facing
transitive axiom reports overall. Those reports are declaration-level proof
checks, not a completion percentage for the published theorem.

## Generalization under review — *not yet verified*

The next proposed source-facing result has `p` independently
evaluated ordinary coordinates followed by `q` marked
coordinates, still at intrinsic complete-skew height one.

- #500: the true vector support geometry for the first p roots
  at one early ray level and the last q roots at a later level.
- #501: genuine mixed parameter elements, with exact D₀-word
  and D₂ observed-letter formulas.
- #502: each actual mixed-span point has the resulting
  independent p-vector Hales–Jewett and q-letter representation.
- #503: application of the already verified parameter-vector
  Hales–Jewett theorem to obtain the unconditional c-good word.

All #500–503 statements remain **proposed**, and must pass complete
Lean compilation, finite regressions, source graph and registered
transitive axiom checks before being called verified.

## Full theorem remains open

Neither the verified q-marker result nor the proposed p/q
extension supplies genuine `D₁` up-leaf selections, intrinsic
`k > 1` complete-skew support recursion, arbitrary coordinate
permutations with correct vector length ordering, a relative
refinement theorem on prescribed source spans, or the corrected
quantitative Corollary 22. The printed Definition 24 selector
and Lemma 27–28 induction likewise remain open. The verified
nonconstancy of nonempty Γ₁ residual records on full starred
mixed spans is respected: colours may depend on retained
marked data.

**Next proof obligation if the p/q stack validates:** prove
the converse p/q span coverage and then address either the
relative/refinement version or the D₁ leaf-selection geometry
before attempting the higher-height induction.
