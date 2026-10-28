# Lemma 27: c-goodness, smoothness, and starred-span monochromaticity

**Status: 28 October 2026.** The results below are kernel-checked and
merged through #453, with full Lean umbrella compilation, finite
regressions and transitive axiom audit (1,927 source-facing endpoints).
They do NOT prove printed Corollary 22, Lemma 27, or Theorem 3.

## What the available Ramsey invariant actually says

Definition 11's c-goodness for a mixed product variable word f is the
following implication for x,y in its genuine mixed span:

    same D2 marked points
    + same observed letter at each corresponding D2 point
    ==> same colour.

The whole tuple is recorded as MixedProduct.bulletRecord.
This is a factorization/canonization property, not a claim that the
colour is constant on every corrected starred input in f.span.

In #448 the theorem

    ForwardQFinalEnlargedGoodTransfer.
      eligible_enlarged_target_colors_eq_of_good_record

transfers exactly this record-based conclusion to the corrected
Lemma 27 target class. The key inputs, already verified, are the
actual Q preimage over the true enlarged alphabet
alpha + Fin(m+1), full dependent rooted-word agreement and
representation-independent equality of target observations.
The local c-good Ramsey witness and elimination of the residual
D2 bullet record are still separate requirements.

## Why c-goodness alone cannot yield full starred monochromaticity

The new source-facing file MixedGoodStarredSpanObstruction.lean
contains a constructive, fully generic counterexample:

    colorAtBullet i x = x.words i.1 (x.bulletPoint i).

This colouring is c-good on every mixed variable-word span, by the
definition itself. Choose any actual starred point x in the span
and two different enlarged letters a,b. Re-evaluate just the
variable component at bullet coordinate i using constant a or b,
leaving all D2 marked points literally unchanged. Both resulting
mixed points remain in the SAME genuine f.span. The corrected
starred predicate depends only on those marked points, hence both
points remain starred, while their colours are distinct.

For the genuine forward-corrected Lemma 27 frames and positive
local dimension q, existence of an initial actual starred span point
was already checked in ForwardQFinalEnlargedInducedEvaluation.
Therefore this is not an empty-domain trick. The theorem
MixedGoodStarredSpanObstruction.no_full_starred_monochromaticity_from_good
makes the obstruction precise.

**Qualification:** this generic marked-letter colouring is NOT
claimed smooth for an arbitrary Definition-21 Gamma1/Gamma2
partition. For Gamma2 coordinates, smoothness permits changing
letters inside the marked inclusive successor cone. Any such
colouring must ignore those variations.

## The independent printed Corollary 22 issue is stronger

Corollary22Audit.lean already contains a *smooth* height-one
Boolean counterexample at the exact printed numerical bound:

    d0 = d1 = 0, d2 = 1, b = ell = r = 2, k = n = 1.

At height one the unique marked root is forced. The colour
c(w,t) = w(t) is smooth for Gamma1 = D2, but every nonempty
complete one-variable word has two evaluations with opposite
colours in its starred span. Meanwhile that same small
combinatorial space is c-good for every colouring in the
proper Definition-11 sense.

This is a documented source-text problem; it is not repaired
by either the corrected Q construction or by changing the
alphabet of the mixed Ramsey word. A statement strong enough
for the actual induction must be formulated and proved.

## Verified: smoothness erases every Gamma2 marked letter

Merged PR #451 constructs an actual single-variable reassignment at
a selected Gamma2 bullet marker. It changes only the local
component variable rooted at the original marked D2 point, so
it remains in the genuine mixed span and agrees with the original
word outside that point's inclusive successor cone. The two
inputs are consequently Definition-21 smooth-related.

PR #452 simultaneously normalizes the observed marked letter
at ALL Gamma2 indices to one chosen fallback alphabet letter.
The resulting mixed input is still in the genuine span, its
marked points have not moved, its Gamma1 word coordinates are
unchanged, and it remains smooth-related to the original.
Combining the actual Definition-11 c-goodness and
Definition-21 smoothness gives the verified theorem

    MixedProduct.good_smooth_color_eq_of_reduced_bullet_record

whose premise on two span points is EXACTLY

    same D2 marked points at every coordinate
    + same observed letter at Gamma1 marked points
    ==> same colour.

Importantly, NO equality of the Gamma2 observed letters,
full unstarred span constancy, or starred-domain
monochromaticity is used. The proof neither assumes nor
produces an additional Ramsey word.

PR #453 transfers that result through the verified genuinely
enlarged corrected starred Q preimage. It defines a reduced
target D2 record that retains every selected local marked point
and only Gamma1 observed letters, and proves

    ForwardQFinalEnlargedReducedGoodTransfer.
      eligible_target_colors_eq_of_reduced_record

for any supported, same-complete-signature target pair refining
the actual enlarged final word. The intrinsic-root simplicity
interface supplies the smooth total colouring; a local c-good
mixed word is the remaining genuine Ramsey hypothesis.

### Why the reduction matters, and what is still not implied

Definition 11 on its own retains both marked points and observed
letters at ALL D2 indices. Smoothness permits removing only the
Gamma2 letter information. Gamma1 components remain entirely
word-fixed by smooth comparisons, so their observed letters
can remain colour-relevant. Gamma2 marked points themselves
are unchanged under smooth comparisons, so their positions
can also remain colour-relevant. The theorem therefore cannot
be strengthened to full starred monochromaticity by the
arguments so far.

The remaining induction has to canonize the residual record,
or prove that the relevant target class has a fixed record.
The target record in PR #453 was first expressed using a
certified existential Q preimage. An explicit target-derived
record and its independence of the Ramsey-word support choice
are being checked separately, and must not be marked verified
until their full Lean audits pass.

## Remaining blockers

1. A corrected quantitative source-facing smooth mixed Ramsey
   theorem with the right enlarged alphabet and the needed
   canonicity conclusion. The exact printed Corollary-22 bound
   cannot be used as it stands.
2. Elimination or permitted retention of the residual D2
   bullet record in the proposed Lemma 27 induction.
3. Identification of the printed Definition-24 selector with
   the verified intrinsic-root extension.
4. Reconciliation of the paper's reverse-lex W_* starred domain
   with the globally forward-corrected Q construction. Naive
   coordinate reindexing has a separate typed counterexample.
5. The numerical and signature transports through Lemma 28,
   Theorem 25 and Theorem 3.

The corrected target Q reverse preimage has been proved for
genuine enlarged local words; these remaining issues concern
Ramsey existence, canonicity and the published formulation,
not merely the representation of a target tree.
