# Adversarial audit of the dual-tree Lean formalization
**29 October 2026; source baseline: merged PR #461 (main `5c80b63`).**

## Scope and evidence

This is an adversarial *repository-wide structural* audit coupled with
a focused *mathematical-interface* audit of the main theorem route.
It is **not** an independent line-by-line mathematical reproof of all
404 individual `DualTree/` source modules. The distinction matters.

- Complete umbrella `lake build DualTree` passes. The source/import
  audit reports 405 modules including the root, 404 reachable local
  sources, no missing modules and no duplicate root imports.
  The default `lake build` checks only `DualTreeCore`, not the
  full proof library; CI explicitly builds both.
- 1,948 *distinct registered* `#print axioms` source-facing
  declarations use only `propext`, `Classical.choice` and
  `Quot.sound`. These are not 1,948 independent proofs of the
  paper and not a completion percentage. Unregistered declarations
  are compiled but are not individually listed in the axiom log.
- The static audit currently finds zero visible `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `partial`, `unsafe`
  or `native_decide` constructs in audited sources.
  In #460 this was strengthened from a *report-only* diagnostic to
  a CI-failing gate for missed local modules and forbidden patterns,
  with miniature-repository negative regression tests. The lexical
  scanner is still not a replacement for a Lean syntax parser.
- The project pins Lean `v4.35.0-rc3`, Mathlib and both dependent
  tree/Ramsey repositories to explicit revisions in `lakefile.toml`.
  Successful CI applies to these pinned versions.

## Critical mathematical findings and remaining nonimplications

### A. The published theorem is NOT yet proved; its literal form is partly false

1. **Printed auxiliary order / Q construction**: the paper's
   reverse-lexicographic order does not preserve its proposed
   canonical map; concrete typed source and Q-order counterexamples
   are already checked. The large forward-lexicographic replacement
   is a *corrected construction*, not an equivalence theorem for the
   original printed domain `W_*`. The repaired order must be stated
   and justified in any corrected paper theorem.
2. **Unary alphabet, Theorem 3**: evaluated-span containment collapses
   for a one-letter alphabet. `Theorem3Audit` and `UnaryMainAudit`
   prove the failure even at arbitrarily large ambient heights.
   Either impose at least two alphabet letters or replace refinement
   by a syntactic definition.
3. **Printed Corollary 22**: `Corollary22Audit` proves a genuinely
   smooth height-one colour separation and the specialized local
   `c`-good one-dimensional witness. However, **the full numerical
   wrapper defining the global `MTHJ` and `CT` thresholds is not
   itself assembled as one Lean theorem**. The manuscript-level
   conclusion that the exact printed bound fails uses those
   additional elementary threshold evaluations. Do not describe the
   whole numerical bound, with its global quantification, as an
   already kernel-checked statement.
4. Other printed issues retained in `audit.tex`: Remark 1's
   extension assertion, Remark 2, a false TGR/PTGR inequality in
   Theorem 25, and the disjoint-set case of Remark 3(ii). These
   cannot be silently repaired by reusing the forward Q lemmas.

### B. Colour transfer is conditional, and the condition is substantial

- `MixedProduct.Good` (Definition 11) canonizes colours only
  relative to all marked D₂ points **and their observed letters**.
  The verified `MixedGoodStarredSpanObstruction` shows that
  `c`-goodness does **not** imply full starred-span monochromaticity.
- Definition 21 smoothness allows erasing the letters at Γ₂
  markers but not the Γ₂ points or Γ₁ letters.
  `MixedGoodSmoothReducedRecord` proves the exact reduced
  statement; the genuine enlarged Q target transfer now uses it.
- A `LocalMixedWord` for which `Good total f` holds must still be
  **constructed by the missing corrected Ramsey step**.
  Passing `hgood` as a theorem premise is not a proof of that step.
- Equality of target reduced records has not been forced between
  arbitrary same-signature targets. Invariance of a *fixed target*
  across refinements (#456/#458) is logically different from
  record constancy across *different targets*.

### C. Newly checked positive bridge, but its exact scope matters

- #457 projects the D₂ record onto unique **actual target terminal
  nodes**. The fixed cone projection is injective, so equality
  of projected terminal records is equivalent to equality of local
  D₂ records.
- #458 proves terminal-record independence of the choice of local
  mixed Ramsey word, auxiliary constants, dimension and signature
  cut witness, **for one fixed target** supported in both.
- **#461 adds a genuine cross-target statement**: if two eligible
  targets with complete corrected signatures have the same
  `tree.toFinset` (they may enumerate their vertices differently),
  their terminal components agree at every D₂ index. When
  `Γ₁ = ∅` there are no remaining marked letters, hence their
  *entire* terminal records agree and a c-good smooth pullback
  gives equality of target colours. The proof uses the verified
  common interior of literal-same-signature targets, not an
  assumption of equal list order.
- This is a **fixed-tree fibre result**, not a statement that a
  Ramsey refinement forces all eligible targets to have the same
  tree. For general Γ₁, residual encoded marked letters remain.

### D. Two dangerous representation/canonicity shortcuts

1. The `Observation` used for Q target preimages correctly
   forgets tree-list permutations and dependent subtype proofs
   while retaining the full rooted word. Arbitrary functions on
   raw `StarredWord` records are **not** proved invariant under
   such representation changes. Any manuscript colour transfer
   should go through `Observation` or explicitly assume invariance.
2. `encodeProjectedOutputSymbol` is a choice of an enlarged
   auxiliary letter realizing a target symbol. Its correctness
   after decoding is verified; **extensional equality of chosen
   letters for two different targets with equal output symbols
   is not yet proved**. In particular, the label 'canonical'
   in the reduced Γ₁ record must not be read as an unproved
   representation-independent normalization of all auxiliary
   preimages. A deterministic encoder or an extensionality
   theorem is a natural next lemma.

### E. Q coverage, canonical selector, and the final induction

- The corrected Q has a genuine enlarged starred target preimage
  with full observed node set and rooted word agreement, under
  explicit complete-signature, final-support and evaluated-span
  hypotheses. This is not unconditional reverse span coverage.
- `ForwardQFinalReverseCoverageCriterion` isolates the
  `RetainedRootsAreOld` hypothesis needed for unrestricted
  evaluated-Q coverage. There are proved obstructions when
  extra early roots remain independently assignable. The
  signature-compatible/anchored coverage results must not be
  substituted for unrestricted inclusion.
- `ForwardQPaperSelectorRecursion` gives a conditional criterion
  (the printed selector satisfies intrinsic root/successor laws
  *on real Q images*). These laws are **not** derived from the
  published Definition 24. The (B_1/B_2) induction cannot
  currently invoke them without a correction or new proof.
- Theorem 13's complete gluing construction is not formalized:
  `GluingAudit` checks the exact-length tail-domain error,
  not the full theorem. Likewise, Lemmas 27/28, Theorems 25/3
  and the product Theorem 29 remain unproved as complete results.

## Repair priorities (ordered)

1. **Mathematical bottleneck:** state an actually valid finite
   smooth mixed Ramsey theorem over the true enlarged alphabet
   that supplies enough residual-record control for the Γ₁/Γ₂
   induction. The known c-good/monochromaticity counterexample
   must be part of its specification test. Do not infer its
   existence from the currently conditional colour-transfer APIs.
2. **Canonicity:** make the published Definition-24 selector
   explicit on arbitrary semi-complete supports, prove root and
   successor laws on corrected Q outputs, and establish whether
   the Γ₁ encoder is extensional across equal observed symbols.
3. **Source-to-corrected theorem:** fix the auxiliary order,
   the unary-refinement convention and the Corollary-22 bounds,
   then formalize Lemma 27's whole iteration, Lemma 28's
   signature transport, and Theorems 25/3. Keep numerical
   thresholds separate until the qualitative theorem is sound.

## Audit acceptance policy

A lemma is **Lean verified** when it compiles on the full umbrella,
has no prohibited or nonstandard axioms and its exact hypotheses are
stated. It is **paper verified** only after a separate comparison
with the printed definition and all intermediate hypotheses. A
counterexample to an auxiliary printed assertion must not be called
a counterexample to the whole dual-tree Ramsey phenomenon.

The next progress measure should be named *remaining proof obligations*,
not a percentage calculated from the 1,948 registered endpoints.
