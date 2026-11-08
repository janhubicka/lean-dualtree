# Track D continuation — the sharp induced-Q support boundary

**8 November 2026.** Repository: `janhubicka/lean-dualtree`.
Depends on the verified and merged corrected source-relative Q transfer
(PR #527, main commit `e77170d1d118d3bba165c3c5107ef94b14717441`).

## What the prior transfer proves

For every admissible source frame, every *supplied* genuine enlarged local
mixed word, and any original-alphabet fallback, the constructed final word
is an actual complete skew variable word. It syntactically refines the
ambient word, retains every old root and symbol through the inclusive
forward cut, and has nonempty **evaluated** span. Every starred target with
the full source finite-set signature, whole-word syntactic refinement and
whole-tree support inclusion has a genuine corrected-starred Q preimage.
For q >= 2 an induced starred Q output is such a target. A positive
target exists if and only if q >= 2.

## Stronger geometric consequence proved in this continuation

The new file
`DualTree/ForwardQFinalInducedSupportThreshold.lean`
states and proves for **each** assignment `σ` of original letters to
the final variable roots, at any positive local height q:

1. The actual induced corrected Q output is an eligible
   `SourceRelativeSetTarget` if and only if `2 ≤ q`.
2. **All vertices** of that induced Q tree lie in the actual
   interpolated final support if and only if `2 ≤ q`.
   The complete set signature and full-word syntactic refinement
   already hold without this inequality; it is *only* whole-tree
   support containment that fails at q = 1.
3. Equivalently, the induced Q tree has some vertex outside
   the final support if and only if `q = 1`.
4. At q = 1 an explicitly chosen induced starred input exists in the
   genuine local mixed span **and** its Q tree has an unsupported vertex.
   This is a nonvacuous failure: the local mixed span and the final
   evaluated-word span are not being declared empty.

The first three statements are uniform across source frames,
auxiliary constants, alphabets with a fallback (including unary),
and assignments `σ`. They have the actual forward starred point
ordering, and do not identify the incorrect printed reverse-lex
domain with the corrected one.

Proof dependencies are the verified
`ForwardQFinalInducedSignature`,
`ForwardQFinalInducedRefinement`,
`ForwardQFinalInducedSupport`, and
`ForwardQFinalTargetHeightBoundary` modules. No conditional Ramsey
witness is disguised as existence. Four declarations have separate
transitive-axiom registration.

## Why this matters for Lemma 27

Any proposed reuse of the corrected Q interpolation at local height
one must either change the final support geometry or explicitly remove
the fixed-signature target condition; mere nonempty evaluated span
cannot justify the target-class witness. The restriction q >= 2
agrees with the paper's intended parameter difference q = M - m'
when m' < M-1.

This is a *geometric boundary check*, not a proof of the missing
local c-good Ramsey existence, residual Gamma-1 colour control,
finite height bounds, or the Lemma 28/Theorem 25 induction.

## Validation

The precise branch head and exact-head CI status should be recorded
after the full Lean and source-audit workflows finish. The added
proof endpoints are subject to the same allowed-axiom restriction as
the rest of the library.
