# Adversarial Lemma-27 audit: Γ₁ records cannot be made constant on a full starred mixed span

**30 October 2026.** Proof branches #472–473 introduced the source-facing
claims below; their full Lean/axiom audits must pass before labeling them
kernel-verified. The full dual-tree theorem is still open.

## The distinction that matters

Definition 11's `c`-goodness is a statement about the *colour of each
mixed-product point*, not about the marked coordinates being constant.
On a genuinely generated local mixed span, it allows the colour to
depend on all D₂ marked points and their observed letters. Definition
21 smoothness removes the observed letters at Γ₂ points but does not
remove the Γ₂ points or the Γ₁ observed letters.

Consequently the exact residual record is

    i ↦ (bulletPoint_i, if gamma1 i then some(word_i(bulletPoint_i))
                         else none).

Its equality criterion is precisely
- equality of the D₂ marked points at **all** selected indices; and
- equality of observed letters only at **Γ₁** indices.

This is the local source of the intrinsic target-leaf/rooted-symbol
record verified in #464–470.

## The stronger proposed record-constancy conclusion is false

Take any genuine local mixed variable word `f`, any point `x ∈ f.span`
and a selected D₂ coordinate `i ∈ Γ₁`. The current Lean repository
already has
`MixedGoodStarredSpanObstruction.recolorBullet`, showing that assigning
a fresh constant letter to the genuine variable at `x.bulletPoint i`
keeps the whole element in the actual `f.span`. It leaves **every**
marked point unchanged and changes the observed letter at `i` to
whatever alphabet letter was selected.

If there are two distinct alphabet letters `a ≠ b`, the two
resulting elements have different residual records. This is true
irrespective of how the colouring was chosen.

In the genuine corrected Lemma-27 enlarged alphabet
`β = α ⊕ Fin(m+1)`, two distinct letters exist automatically:
`Sum.inl fallback` and `Sum.inr ⟨0, ...⟩`. For a positive local
dimension `q`, the verified
`ForwardQFinalEnlargedInducedEvaluation.enlargedInducedStarredInput`
constructs an actual starred point inside `f.span`. The starred
condition depends exclusively on the marked points, so both
recolourings remain **starred**. Thus whenever Γ₁ contains an actual
D₂ marker, the reduced record is not constant on the full corrected
starred portion of `f.span`, for *any* such `f`.

This structural obstruction is stronger than saying that one
particular colouring is not monochromatic. The observed-letter
colouring `x ↦ x.words i (x.bulletPoint i)` is itself c-good on every
mixed word. **It is NOT claimed smooth for arbitrary Γ partitions.**
The distinct height-one smooth Corollary-22 counterexample remains
separately checked; this argument alone does not refute the full
dual-tree Ramsey theorem, and does not establish that the eligible
target class includes every local starred Q image.

## The corrected positive goal is factorization through records

When `c` is both c-good on a mixed word `f` and globally smooth,
the previously verified simultaneous Γ₂ normalization gives

    reducedRecord(x) = reducedRecord(y)  ==>  c(x) = c(y)

for actual points of `f.span`. It does NOT give
`reducedRecord(x)=reducedRecord(y)` for arbitrary points.

#473 constructs the actual Option-valued record colouring

    record ↦ some(c(chosen representative))
                  if the record is realized in f.span,
             none otherwise.

Under the existing c-good + smooth hypotheses this agrees with
`some(c x)` at every realized record. It is unique on realized
records among partial colourings agreeing with c, and requires no
`Nonempty γ` assumption. This is the appropriate factorization
API for the later induction. It does not itself produce the c-good
word or a finite Ramsey bound.

## Corrected next steps

1. Prove the **real finite mixed Ramsey existence theorem** supplying
   a genuinely enlarged local `c`-good word, with all required
   quantitative dependencies. Do not strengthen its conclusion to
   constant residual Γ₁ records on the full starred mixed span.
2. Transfer the resulting *record-dependent* colouring through the
   corrected Q preimage onto the direct target-leaf/rooted-symbol
   record `targetLeafRootedRecord` (#468–470), without forgetting
   whether `Γ₁` or `Γ₂` is being handled at each induction stage.
3. Identify the printed Definition 24 selector with the corrected
   Q-image selector and repair the published reverse-lexicographic
   starred domain before completing Lemma 27/28 and Theorems 25/3.

This note distinguishes the precise false strengthening from the
still-open, potentially valid induction architecture.
