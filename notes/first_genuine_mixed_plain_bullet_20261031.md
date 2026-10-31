# The first genuinely mixed D₀/D₂ Ramsey theorem in Lean

**31 October 2026.** PRs #486–490 are merged and full CI-verified.
PR #491 adds the converse span coverage / nonvacuity check and
remains CI-pending until its own Lean and transitive-axiom audits pass.

## Precisely what is proved

In the actual `MixedProduct.Element` and
`MixedProduct.VariableWord` API, take the two-coordinate kind

    kind(0) = plain (D₀),   kind(1) = bullet (D₂),

with no D₁/up coordinate. For every branching `b > 0`, every
finite alphabet `β`, every finite colour type `γ`, and an
explicit fallback letter `fallback : β`, there is a finite
ambient tree height `n` such that **every** colouring

    color : Element b n 2 β kind → γ

admits an actual 1-complete-skew mixed variable word

    f : MixedProduct.VariableWord b n 2 1 β forwardAux kind

on whose TRUE mixed span `Good color f` holds, exactly as
in the paper's Definition 11. The theorem

    PlainBulletRay.exists_good_plainBullet_height_one

is an existence theorem, with no supplied `hgood`,
`hmono`, target record, or postulated mixed Ramsey input.
It makes no claim about the printed quantitative Corollary 22.

## Why the same-support argument would be invalid

The all-D₀ vector Hales–Jewett theorem has a single support
root for every component. In the mixed D₀/D₂ case,
an adversarial colouring can observe the D₀ word at the
D₂ marked variable root. If that point also carries the
D₀ variable, varying the D₀ assignment may change colour
while the D₂ observed letter remains fixed—so the proposed
c-good conclusion would fail.

The corrected construction therefore uses two DISTINCT
singleton support roots, with ordered ambient lengths.
If the flat Hales–Jewett word uses N slots and its first
variable occurs at index r < N, the D₀ support root is
the node at position r on an all-zero tree ray, and the
D₂ support root and marked point are the **later** node
at position N. All D₀ variable occurrences lie among
the earlier N ray slots. The D₂ word is variable only at
its later root and is a fallback constant elsewhere.

PR #487 verifies the full source-facing
`VectorSkew.vectorCompleteB` predicate for ordered
pairs of singleton supports, not just the separate
componentwise KVariableWord completeness.
PR #488 constructs the genuine mixed word with real
D₂ support/marked-point membership and empty D₁ data.

## The Ramsey proof and exact residual dependence

PR #486 imports a genuine finite-parameter Hales–Jewett theorem
from Mathlib through DualTree's precise `SpanAudit` semantics.
For finite parameter set θ and finite γ, it applies ordinary
multidimensional Hales–Jewett to the **function-valued**
colour type `θ → γ`. Thus a single proper Hales–Jewett
variable word is monochromatic at EACH fixed parameter θ,
but the resulting colours may differ between parameters.

For the mixed theorem, θ is the D₂ marked-letter alphabet β.
The colouring used to invoke Hales–Jewett is

    C(u)(a) = color(parameterElement(u,a)),

where u fills only the D₀ ray slots and a is the independent
letter of the D₂ variable at the fixed later root.

PR #489 proves that every actual mixed-span point equals
one of these parametrized elements, with a D₀ Hales–Jewett
assignment and an independent D₂ letter. In particular
its marked point equals the fixed last ray root, and
its observed letter is exactly a. Equality of D₂ letter
observations therefore permits Hales–Jewett to equate
colours for arbitrary choices of the D₀ assignment.
No constancy in a is assumed, so the earlier Γ₁
residual-record nonconstancy obstruction is respected.

PR #490 packages this as a genuine `Good color f`
theorem for the source-facing mixed product.

PR #491 proposes the additional converse: every pair
of D₀-variable assignment and D₂ letter is realized
by an ACTUAL span element, and the span equals the
whole parametrized family. Once its own CI is green,
it will rule out any vacuity/coverage concern.

## Remaining mathematical gaps

This is a nontrivial positive instance of the mixed
Ramsey theorem, but it is only the **two-coordinate
(D₀,D₂), intrinsic height-one, initial ambient word**
case. It does NOT prove:
- a general finite mixed kind `Fin d → CoordKind`,
  with arbitrary numbers/orderings of D₀ and D₂;
- any D₁/up-leaf selections or their full skew conditions;
- k-complete skew supports of intrinsic height k > 1;
- the relative/refinement conclusion for arbitrary
  prescribed input variable words;
- the quantitative Corollary 22, exact Definition 24
  canonical selector, Lemma 27/28 induction or Theorems
  25, 3, 29.

**Next promising proof target:** extend the finite
parameter space to β^{D₂}, use ordered *separate*
blocks for all D₀ variable slots and D₂ marker roots,
and preserve the full vector 1-complete skew length
ordering. Later add D₁ leaf constraints and the
higher-height complete-skew recursion.

A registered source-facing axiom endpoint count measures
checked Lean declarations, not theorem-completion percentage.
