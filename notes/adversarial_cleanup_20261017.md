# Dual-tree adversarial cleanup and build split (17 October 2026)

## Verified baseline and scope

The most recent confirmed full-build baseline before this patch is main
`e91d9968` (PR #355; both Lean and source-audit workflows green), which
checks 1,551 distinct selected transitive-axiom reports. PR #356
(`ForwardQFinalOldNewEqualRank`, four additional reports) had two green
CI checks and was merged as `aecbe5c7`. The resulting 1,555-report
main build should be checked independently after the merge.

PR #354 was closed as superseded by #355: its actual proof file has the
*identical Git blob SHA* in main. Its closure removes only a stale PR, not
the theorem. Retain historical counterexample files: the printed
reverse-Q obstruction and the forward repair regression tests are
mathematically important negative certificates.

## Findings: proof trust and mathematical audit

* The full Lean umbrella transitively reaches all 261 existing source
  modules; there is **no unreachable file** certified safe to delete.
  The earlier root-import compaction removed redundant edges without
  dropping modules, and the earlier placeholder-word dead-scaffold
  elimination was checked against both imports and axiom endpoints.
* The source scan finds no active `sorry`, `admit`, `axiom`,
  `opaque`, `unsafe`, or `native_decide`. The curated checker
  accepts only Lean's standard classical/propositional axioms.
  **Neither test establishes faithfulness to every printed theorem.**
* The source-facing `Frame` assumes a **forward-order repaired**
  complete ambient tree; it is not the printed reverse-order starred
  hypothesis. Naive reversal/reindexing was separately falsified.
  Therefore the validated forward-Q lemmas do not silently complete
  Lemma 27 in the paper's original generality.
* The rank budget has two bands: frontiers at m admit all local q
  levels, while frontiers at m+1 omit the top local level. In
  particular q=1 permits no selected root above an m+1 frontier.
  All cross-frontier statements must split these two cases, rather
  than treating them as uniformly complete.
* After #356, the retained/retained and retained/projected length
  cases of final skew clauses (ii)/(iii), plus same-frontier
  projected/projected strict-rank case, have proofs. Equal-rank and
  strict-rank projected/projected comparisons ACROSS DISTINCT
  frontiers, final skew witness (iv), the fully assembled f',
  original Definition 24 selector transport, and the Ramsey iteration
  are not proved. Do not label T'_M globally complete/skew yet.

## Measured CI performance and safe change

The 17 October successful main CI job restored a roughly **738 MB**
Lean toolchain cache and a roughly **2,062 MB** Lake workspace cache.
The Lake restore alone took roughly 65 seconds
(03:46:21–03:47:26 UTC), whereas the cached full build completed in
seconds after its cached dependencies were ready. This is a
CI cache-transfer bottleneck, not evidence that 261 source modules
are all slow to elaborate. An uncached local development build can
still be much more expensive.

**No proof-bearing source module is removed in this pass.** Instead,
`DualTreeCore.lean` exports the reusable foundational definitions,
and `lake build` builds this small default target. For focused
research work, use `lake build DualTree.ForwardQFinal... ` or the
particular source module under modification. For complete
validation, use `lake build DualTree`: CI now runs this explicitly
before the original full finite regressions, import-graph audit, and
1,555 selected transitive-axiom reports.

The full umbrella `DualTree.lean` and its transitive minimal-cover
enforcement are retained unchanged. This build split trades a smaller
**default developer build** for an explicitly named comprehensive
build; it does not shorten the comprehensive CI proof check. No
unmeasured speedup percentage is claimed.

## Follow-up gates

1. Prove the distinct-frontier projected/projected skew comparisons,
   including same-final-rank lex orientations and both frontier rank
   bands. Before applying existing vector-skew length lemmas, verify
   that local rank gaps imply the necessary **ambient T-rank** gaps;
   a one-unit shift between m and m+1 is a genuine boundary case.
2. Establish the final skew branching witness (iv) with the q=1
   degenerate band explicitly accounted for, not a fabricated child.
3. Prove the full stitched ambient word f', its span inclusion, and
   source-simple-to-smooth coloring transport for the genuine
   Definition 24 selector on arbitrary relevant semi-complete U.
4. Iterate the verified Lemma 27 interface to Lemma 28, Theorem 25
   and Theorem 3 only after these hypotheses are discharged.
