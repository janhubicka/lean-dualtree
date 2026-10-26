# Lemma 27: genuine enlarged-alphabet Ramsey-word handoff

Status: **Lean verified through merged PR #440 (26 October 2026)**.
The full dual-tree theorem is NOT formalized. This note concerns the
globally corrected forward-lex construction only. The printed
reverse-lex starred-domain discrepancy remains independent.

## The alphabet mismatch exposed by the audit

The paper invokes its smooth mixed-product Ramsey result over the
ENLARGED alphabet beta = alpha plus Fin(m+1). The earlier corrected
interpolation instead used a local word over the original alpha,
then injected its fixed constants into the enlarged alphabet.
The latter cannot represent fixed auxiliary beta constants.

PR #433 verifies this algebraically. In particular any beta-local
variable word with a fixed auxiliary constant cannot be the
literal constant lift of an alpha-local word. The corresponding
evaluated word-span containment also fails when such a constant
is fixed. This does NOT refute Corollary 22 or its conclusion;
it shows why its unrestricted witness could not simply be
inserted into the older alpha-only final-word construction.

## Verified corrected construction

PR #434 constructs the genuine local symbol decoder:
- an original alpha fixed constant remains unchanged;
- a fixed auxiliary j is decoded using the genuine visible-ancestor
  R_i, possibly into an OLD retained variable root of final f';
- a selected local variable maps to its distinct projected final
  root P_i(v), with excluded roots constantized by the rank budget.

Every emitted variable is verified to prefix the actual projected
ambient P_i(z), including the fixed-auxiliary case. No Hall
identification between independent local variables and the old
source variables is postulated.

PR #435 builds the total global root-compatible substitution and
the actual ambient final word over alpha from these beta-valued
local components. It fixes every selected rank-budget final
root, has exactly the complete-skew final support T'_(m+q),
and has evaluated span included in the ORIGINAL ambient span.
Every safe projected f-root reads exactly the genuine decoded
local beta-word symbol. These are source-faithful algebraic facts.

PR #436 generalizes the exact target-terminal D2 inverse
address and support-membership statements to an arbitrary
local constant alphabet beta, retaining the original literal
source markers and corrected sorted frontier indices.

PR #437 constructs a genuine beta-valued enlarged mixed-product
input from any selected final-root assignment. Every coordinate
word is an actual local-component evaluation, so fixed auxiliary
constants remain intact. For q>0 the true intrinsic-zero
D2 support roots satisfy the corrected starred singleton-vector
order, giving a genuine member of the local beta-mixed span.

PR #438 compares evaluations of the ACTUAL corrected fibrewise
Q and the genuinely enlarged f' on every safe projected root
and its ENTIRE original ambient f-variable fibre. It includes
the nontrivial fixed auxiliary constant case, where R_i is
evaluated against the old source roots or their retained copies.

PR #439 derives the required old-root assignment compatibility
from the existing canonical anchoring map, for arbitrary old
source assignment tau and arbitrary base final assignment
sigma0. No independent new projected root is frozen.

Verified source files:
- ForwardQFinalAlphabetLiftObstruction.lean
- ForwardQFinalEnlargedLocalSymbols.lean
- ForwardQFinalGlobalEnlargedWord.lean
- ForwardQFinalPolymorphicTargetD2.lean
- ForwardQFinalEnlargedInducedEvaluation.lean
- ForwardQFinalEnlargedProjectedEval.lean
- ForwardQFinalEnlargedAnchoredEvaluation.lean
- ForwardQFinalEnlargedWholeDomainEvaluation.lean

## Remaining requirements

**Verified whole-domain forward evaluation (PR #440).**
For every old-source assignment and arbitrary base final-root assignment,
the canonical anchoring map synchronizes the retained old roots while
preserving independent new projected variables. Lean proves the
actual corrected fibrewise Q evaluated word equals the genuine
enlarged f' evaluated word at EVERY bounded ambient position:
original ambient constants, early source fibres, safe projected
fibres including fixed auxiliary constants, and late unsafe fibres.
The constructed genuine enlarged starred mixed input lies in the
local Ramsey word span, and its Q evaluation lies in the
enlarged final word span. This is forward evaluated coverage
under anchoring, not unrestricted independent reverse coverage.

**Exact starred target preimage.** The earlier theorem reconstructs
each supported, same-complete-signature alpha-only target with
the exact rooted word and a genuine corrected starred mixed input.
The marker-to-D2 geometry now works for arbitrary beta. Extending
the entire dependent-word preimage to the NEW enlarged final f'
is still an independent proof task. Unrestricted coverage of the
whole independently evaluated final f' span is NOT required and
is in fact obstructed by extra retained early roots.

**Ramsey theorem and manuscript interface.** Connecting the true
Corollary-22 enlarged witness and numerical parameters to this
corrected construction, reconciling printed reverse-lex W_* with
forward W_*, identifying the published Definition-24 selector,
and carrying Lemmas 27–28 through Theorems 25 and 3 remain open.
Naive starred-coordinate reindexing is refuted by a verified
typed counterexample.

These are theorem-completion blockers, not mere documentation
or CI problems. The new results verify a corrected local
construction but do not establish the paper's printed theorem.
