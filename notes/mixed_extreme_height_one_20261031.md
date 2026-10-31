# Mixed-product Ramsey verification: the two height-one extreme partitions

**31 October 2026.** This note distinguishes the genuinely verified
all-`D₀` case (merged PR #483) from the proposed all-`D₂` case
(PR #484, awaiting the full Lean build at the time of writing).

## All-D₀: a genuine positive Ramsey theorem

In `MixedProduct.allPlainKind d`, every coordinate is ordinary.
The `D₁` and `D₂` index types are propositionally empty.
The constructions in `AllPlainMixedRamsey.lean` transport a
genuinely vector-complete-skew variable word to an ACTUAL mixed
variable word and prove the exact equivalence

    x ∈ mixedSpan(f) ↔ x.words ∈ vectorSpan(f.vector).

There are no dummy leaf lists or marker points. The existing
unconditional Hales–Jewett-derived vector 1-complete-skew
Ramsey theorem produces a mixed word whose entire span is
monochromatic for every finite colouring. The checked
`GoodNoBullet` equivalence then yields an actual Definition-11
`c`-good witness. Both conclusions are unconditional
existence statements (the finite ambient height is not
specified numerically), not assertions predicated on a
pre-existing `hgood` witness.

This is the `D₁=D₂=∅`, intrinsic dimension `k=1` case.
It does not establish the relative/refinement version for
an arbitrary pre-existing k-complete-skew word, nor height
k>1.

## All-D₂: marked-letter dependence is allowed

For `allBulletKind d`, there are no ordinary or D₁
coordinates. At ambient tree height one, the only bounded
node is the empty root. All D₂ marked points are therefore
forced to that root. Equality of their observed word letters
already determines the whole mixed element, and so EVERY
colouring is Definition-11 c-good on EVERY mixed span of
the indicated type. This does **not** say the span is
monochromatic: the colour may distinguish evaluations of
the marked D₂ root variables.

The proposed `AllBulletMixedRamsey.lean` supplies an
explicit nonvacuous witness: one genuine root variable in
each component, full vector 1-complete skew support, and
genuinely empty D₁ leaf-index data. Its existence and
Good statements require no finite-colour hypothesis.
They must pass the full Lean and axiom checks before
being marked validated.

## Why the full theorem does not follow

Combining independently proved all-D₀ and all-D₂ extreme
cases does NOT produce a simultaneous mixed `D₀ ∪ D₂`
Ramsey theorem. The required refinement must hold the
marked D₂ data as controlled parameters while
canonizing dependence on the D₀ words, with the
complete-skew geometry preserved. D₁ adds an independent
up-leaf selection problem. Increasing intrinsic height
from one to k>1 introduces complete branching supports
and cross-coordinate rank/ambient-length constraints.

The Γ₁ reduced record in the enlarged alphabet generally
cannot become constant on the full starred mixed span:
merged #472 proves this. The valid target is **colour
factorization relative to residual marked-point/Γ₁-letter
records**, through the merged #473–474 interfaces.
The printed Corollary 22 monochromaticity bound cannot
be restored by simply joining these two base cases.

## Suggested next implementation steps

1. Formalize a *parametric* vector-height-one Ramsey
   theorem for a mixed partition containing D₀ and D₂:
   control all finite tuples of D₂ marker-letter
   values as parameters while refining the D₀ words.
   Avoid assuming the selected D₂ roots are known
   before applying flat Hales–Jewett.
2. Extend this to D₁ leaf sets with the exact
   `up_support_skew` condition.
3. Build the higher-height complete-skew support
   recursion, then transfer the actual c-good result
   into the corrected Q/target-leaf factorization.
4. Check the published selector and reverse-lex
   corrections independently before completing
   Lemma 27/28, Theorems 25/3/29.

Do not interpret the registered source-facing axiom
report total as a percentage of the paper verified.
