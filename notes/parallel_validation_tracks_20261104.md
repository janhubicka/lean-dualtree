# Dual-tree Ramsey theorem: adversarial status and independent tracks

**Audit checkpoint:** 4 November 2026. **Verified baseline:** `main` commit
`c9f2326f5880ae3b062b53812f41b022713578c4` (merged #511). Both
the full Lean workflow and source/axiom audit passed. There are 444
`DualTree/*.lean` modules, excluding the root umbrella, and **2,168
distinct registered source-facing transitive-axiom endpoints** on main.

**IMPORTANT:** The endpoint count is not a percentage of the published
theorem. It covers selected declarations, not every public theorem or
its faithfulness to the printed paper. This is a focused structural and
mathematical-interface audit based on current source, CI, and prior
adversarial notes; it is **not** an independent line-by-line proof
verification of all 444 modules.

Reviewed PR #512 (true interleaved no-D1 mixed vector word) and PR #513
(actual interleaved parameter elements) passed their full Lean and
source/axiom checks after the implicit-height repair. **As of this
checkpoint both remain open and UNMERGED**. Their stacked endpoint
counts are respectively 2,178 and 2,185. The earlier attempted merge
of #512 received an in-progress response/timeouts; do not assert a
merge until Github explicitly reports it.

## 1. Adversarial mathematical verdict

### Verified positive subtheorems

- Unconditional Definition-11 c-good existence at intrinsic k=1 with
  p ordinary D0 coordinates followed by q marked D2 coordinates, no
  D1; includes independent flat Hales–Jewett substitutions, exact
  full span and nonvacuity, and unique factorization through observed
  marked letters (merged #500–506).
- Legitimate arbitrary D0/D2 interleaving geometry at k=1:
  strictly ordered singleton roots, fixed D2 marker root variable
  words, exact disjoint shifted-ray slot decoder, actual D0 shifted
  Hales–Jewett evaluation and uniform flat Hales–Jewett on actual
  plain/bullet subtypes (merged #507–511).
- Extensive corrected-forward Q geometry, selector and Hall
  **conditional** interfaces; these are valuable but should not be
  conflated with the full relative Ramsey construction.

### Known proof/statement blockers

1. **Printed auxiliary order / Q:** reverse-lex Q and naive
   forward reindexing fail on typed starred examples. Forward-order
   constructions use a different stated domain; source equivalence
   remains open. Evidence: `ForwardQStarredOrderReindexObstruction`,
   `QLengthStarredCoordinateOrder`.
2. **Unary theorem/refinement:** evaluated-span inclusion cannot see
   variable support over a singleton alphabet; the arbitrary-height
   obstruction is tracked in `UnaryMainAudit` and
   `Theorem3Audit`. A valid target must impose nondegeneracy or use
   suitable syntactic refinement.
3. **Printed quantitative Corollary 22:** a smooth height-one
   separation and local c-good fixture are kernel checked in
   `Corollary22Audit`, but its GLOBAL numerical MTHJ/CT wrapper is
   not yet a single checked theorem. Do not claim that global
   statement kernel-refuted solely on this file.
4. **Lemma 27 printed construction:** frontier tail domain can
   overflow; a claimed R_i surjection can be cardinally impossible;
   occurrence-based freezing is not uniform substitution.
   `Lemma27Audit` verifies these local defects.
5. **Q reverse span:** anchored forward evaluation does not imply
   `span(f') ⊆ Q(span(f_i))`. Under a source-variable collapse
   hypothesis the reverse inclusion has a proved two-letter
   obstruction (`ForwardQFinalEarlySpanObstruction`).
6. **Enlarged alphabet:** finite smooth mixed Ramsey selection
   allows fixed auxiliary constants in the enlarged alphabet,
   whereas current interpolation lifts original-alphabet constants
   only (`ForwardQFinalAlphabetLiftObstruction`). A genuine bridge
   or explicitly restricted Ramsey theorem is required.
7. **Occurrence Hall / D2 order:** Hall conditions and selected
   bullet-length order have verified iff/conditional interfaces,
   not a global proof they are automatically satisfied by the
   manuscript's local Ramsey word.
8. **Definition 24 selector:** A/source-R marker correspondences
   are verified in corrected frames, but canonical paper I_U
   identification and its root/successor laws on arbitrary relevant
   starred inputs are not closed. Γ1 residual record letters need
   factorization, not false global record constancy.
9. **Final theorems:** the standalone Lemma 28, Theorem 25,
   Theorem 3 and product Theorem 29 proofs have not been assembled;
   Theorem 13 gluing and quantitative estimates remain distinct
   proof gaps. See `notes/adversarial_full_audit_20261029.md`.

These findings target the printed proof or specific attempted
inferences, not every possible corrected dual-tree Ramsey theorem.

## 2. Independent tracks (one issue + branch each)

| Track | Issue | Branch | First independently checkable output | Dependency for final integration |
|---|---|---|---|---|
| **A: interleaved k=1 Ramsey** | [#514](https://github.com/janhubicka/lean-dualtree/issues/514) | `track-a/interleaved-k1-ramsey` | Genuine actual mixed-span forward and converse representations; unconditional Good | Pending CI-green PRs #512/513 must be merged correctly |
| **B: D1 up-leaf geometry** | [#515](https://github.com/janhubicka/lean-dualtree/issues/515) | `track-b/d1-leaf-geometry` | Actual b^k leaf selection and extended-support skew for k=1, with nonempty up span | Independent of A, C, D, E initially |
| **C: k≥2 skew/Ramsey** | [#516](https://github.com/janhubicka/lean-dualtree/issues/516) | `track-c/higher-k-skew` | Genuine all-D0 k=2 complete-skew vector and positive Ramsey theorem | Independent of A/B/D/E initially |
| **D: corrected Q span/refinement** | [#517](https://github.com/janhubicka/lean-dualtree/issues/517) | `track-d/q-span-refinement` | Exact Q inclusion direction and a genuine corrected source-word/refinement bridge | Requires canonical selector only for eventual Lemma 27 assembly |
| **E: selector/smoothness** | [#518](https://github.com/janhubicka/lean-dualtree/issues/518) | `track-e/selector-smoothness` | Paper I_U ↔ corrected R on Q images; genuine source simple→smooth | Independent of D initially using existing Q frame |
| **F: final statement/induction** | [#519](https://github.com/janhubicka/lean-dualtree/issues/519) | `track-f/theorem-induction` | Corrected target statement and explicit typed conditional theorem interface | Final proof depends on A–E; statement work starts now |
| **G: adversarial trust/cleanup** | [#520](https://github.com/janhubicka/lean-dualtree/issues/520) | `track-g/adversarial-trust-audit` | Reproducible source-to-Lean assumption audit and CI/registry coverage report | Fully independent, audits all track outputs |

### Hard ownership boundaries

- A owns only new interleaved mixed-span / c-good / converse modules;
  #512/#513 represent dependencies, not automatically merged code.
- B owns new D1/UpLeaf modules; no edits to A or Q internals.
- C owns higher-k complete-skew and higher Ramsey modules.
- D owns corrected Q source/refinement modules and its counterexamples.
- E owns canonical selector / smoothness transport modules.
- F owns theorem statement, induction interfaces and author-facing
  mathematical corrections. Missing inputs must remain *explicitly
  conditional*, never axiomatized or asserted as finished.
- G owns tests, source-audit tooling, registry and audit notes; source
  theorem changes only as narrowly scoped reviewed repair PRs.

All tracks branch initially from the SAME green main checkpoint and
must rebase through current main without copying stale umbrella imports
or lowering/overwriting existing axiom endpoints.

## 3. Parallel dependency and integration plan

**Wave 1 (genuinely parallel now):** A finalizes the interleaved
height-one Ramsey step; B experiments with D1 leaf sets; C attacks
k=2 independently; D investigates Q source/span and alphabet/order;
E reconstructs canonical selector; F defines corrected target theorem
and induction interface; G performs an adversarial trust pass.

**Wave 2:** Combine A+B into a first positive D1 mixed base case;
then connect C to a higher-k mixed theorem. Combine D+E into a
source-correct Lemma-27 Q/pullback mechanism, independent of the first
mixed geometry integration.

**Wave 3:** F uses the actual higher-k mixed Ramsey existence plus
corrected Q/selector transfer to prove Lemmas 27–28, Theorem 25 and
then a corrected Theorem 3. Quantitative inequalities are separately
validated. G checks the exact cross-track assumptions.

No track should silently replace failure of an original printed
statement with a stronger unproved hypothesis. A conditional theorem
is useful work but does not close its obligation.

## 4. Cross-track interface and mandatory CI gate

Every independently authored PR must provide:

1. **Statement correspondence:** one English sentence stating the
   printed/corrected theorem and a complete exact Lean type, including
   quantifier order, alphabet assumptions, parameter bounds, colour
   scope and starred-domain / refinement relations.
2. **True witnesses:** no passed-in `Good` or nonempty span as a
   substitute for an existence theorem; check exact evaluated span
   and nonvacuity where relevant.
3. **Source semantics:** no accidental equality of different Γ1/D2
   retained records; no unjustified printed↔forward order
   equivalence or reverse Q image coverage.
4. **Kernel trust:** full `lake build DualTree`, the CI finite skew
   and Q regressions, `scripts/check-audit-tex.py`,
   `scripts/audit-lean-library.py --verify-root-minimal` and
   `lake env lean scripts/CheckDualTree.lean` / allowed-axiom
   gate with the distinct registered endpoint count updated.
5. **Adversarial negative examples:** preserve the unary,
   Corollary-22, Q-order, nonuniform substitution, residual Γ1
   and source-variable collapse regressions; add a new regression
   for each newly detected failure.
6. **Trustful status:** report `CI green at head SHA`, `merged
   and green on main`, `conditional`, or `open` accurately.
   No percentage is inferred from code size or axiom count.

## 5. Progress metric

The earlier **35% ±10–15 percentage point** overall completion
estimate is a rough planning judgement. It is not established by
the 2,168 checked declarations or 444 source files. A more honest
track-level dashboard should separately record:

- completed *positive existence theorems*;
- closed *corrected Q/source span interfaces*;
- settled *paper statement / counterexample repairs*;
- compiled but *conditional* helper results;
- integration theorems with all dependencies discharged.

The highest current integration risks are D (Q source/refinement),
E (canonical paper selector), and C (k≥2). A is the shortest
near-term positive theorem target; B and F can work independently.
