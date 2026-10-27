# Lemma 27: genuinely enlarged corrected starred Q preimage and colouring transfer

**Verified through 27 October 2026, merged PRs #444–446.**
The full Lean umbrella, finite Q regressions and transitive axiom audit
passed with 1,895 registered source-facing endpoints. The statements
below concern the **globally forward-corrected** auxiliary order.
They are NOT a formal proof of printed Lemma 27, Corollary 22,
Lemma 28, Theorem 25, or the original dual-tree Ramsey theorem.

## The source-faithful local Ramsey alphabet

The local Ramsey word is genuinely over

    β = α ⊕ Fin(m+1),

not an original α-word whose constants are naively lifted to β.
Fixed auxiliary letters j must be decoded by the actual R_i to
original constants or retained *old variable roots* in the final
ambient α-word. PRs #433–440 establish that full interpolation:
root compatibility, exact rank-filtered support, ambient span
inclusion, legal enlarged starred mixed inputs, and the full
**evaluated** Q/f' equality under canonical old-root anchoring.

The forward evaluated equality alone does not imply the desired
converse for the entire independent final span: retained old roots
may have assignments incompatible with the source refinement.
The target theorem instead restricts to the actual supported,
same-complete-signature starred target class.

## The genuine enlarged starred target preimage is now proved

Fix the corrected source/fibre frame g, local complete mixed-word
f with constant alphabet β as above, and an α-valued starred
target O. Assume

1. branching b>0 and the same **complete corrected signature**
   for the source and O, including the old-root/cut correspondence;
2. all vertices of O.tree lie in the genuine rank-filtered final
   support T'_(m+q), not just the enclosing T;
3. alpha has at least two distinct letters;
4. O.word.span lies inside the actual NEW enlarged final
   interpolation's evaluated span.

The target determines a **unique terminal** at each original
literal source marker. Its safe inverse address in the actual
sorted D₂ component is a genuine local support variable root
even though f has enlarged constants. The coherent enlarged
input makes a SINGLE certified β-letter choice at each local
variable root; every occurrence in the same local fibre gets
that same letter, and genuinely fixed auxiliary constants stay
fixed.

Merged PRs #441 and #443 prove source-facing symbolic fibre
rigidity and the exact target Q finite node SET. Merged PR #444
proves the entire dependent Q output word, at every ambient
bounded position, after the canonical source/target root
equivalence, with an actual mixed-span input.

Merged PR #445 discharges the final D₂-starred-order condition.
Temporarily replacing ONLY β constant letters by one original
fallback α letter preserves all local variable supports,
height-filtered final support and target terminal geometry.
Both selected D₂ tuples project to the SAME unique target
terminals; injectivity of the true local cone projection forces
equality of their marked local roots. The previously verified
target skew/complete-T two-band ordering theorem therefore
transports to the original genuine enlarged D₂ tuple.
No auxiliary fixed constants are actually erased in the
Q preimage constructed over β.

Consequently

    ForwardQFinalEnlargedTargetD2Order.
      exists_typed_enlarged_target_observation_preimage

constructs an **actual typed corrected starred Q input in f.span**
whose Q output has the same finite tree vertex set and entire
variable-root-labelled word as O. Their tree lists are equal up
to permutation rather than falsely claimed to be literally
identical. No added D₂-order assumption survives.

## The conditional colour transfer now uses the right alphabet

Merged PR #446 introduces the exact eligible target family for
the new enlarged final word and proves

    ForwardQFinalEnlargedPairwiseTransfer.
      eligible_enlarged_targets_pairwise_monochromatic.

For a total colouring agreeing on actual corrected starred inputs
with the observation-valued Q pullback, IF a genuine enlarged
local mixed Ramsey word f is pairwise monochromatic on the
**starred portion of f.span**, all supported, same-complete-
signature targets eligible for the corrected final f' have the
same observed colour. This does not require monochromaticity
on the unrestricted mixed-product span, a named common colour,
a separate nonemptiness assumption, or an artificial α-only
literal lift.

Combined with the previously checked intrinsic-canonical-
selector simplicity condition, PR #446 also proves

    ForwardQFinalEnlargedPairwiseTransfer.
      exists_total_smooth_with_enlarged_pairwise_target_transfer.

This is a CONDITIONAL colour-transfer theorem: the actual local
Ramsey word satisfying the required hypothesis and the
quantitative bounds have not been constructed.

## Adversarial issues that are not settled

**The printed Corollary 22.** The existing verified
Corollary22Audit contains a smooth height-one Boolean colouring
for which the stated starred-monochromatic conclusion fails at
the printed bound. The correct distinction between Definition
11's *c-goodness* and full starred-span monochromaticity matters:
c-goodness allows the colour to remember each D₂ marked point
and the letter observed there. A strengthening to full
monochromaticity cannot be silently inferred from the c-good
Ramsey theorem. The corrected statement needed for the actual
global induction has to be determined and proved separately.

**The printed starred domain.** The manuscript orders equal-length
frontiers by reverse lex, while the corrected Q construction
uses forward lex. A typed Lean counterexample shows that naive
reindexing need not preserve the original W_* starred condition.
No equivalence or proof of the printed reverse-lex Lemma 27
is asserted here.

**The induction.** The precise numerical mixed Ramsey parameters,
the relationship to Definition 24's *published* canonical
selector (distinct from the verified proposed intrinsic-root
extension), the Lemma 28 signature transport, and the
global Theorems 25/3 induction remain independently open.

**Unrestricted reverse coverage.** The verified target preimage
covers exactly the eligible, same-complete-signature,
rank-filtered supported target family whose evaluated words
refine the genuine enlarged final f'. It does not claim that
every independent evaluation of the final f' belongs to the
image of the Q-map with an unrelated fixed source
old-root assignment. The separate retained-root obstruction
remains valid.

The corrected local target preimage and conditional colour
transfer are substantial kernel-checked pieces; they must
not be conflated with a completed verification of the paper.
