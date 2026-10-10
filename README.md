# lean-dualtree

Lean 4 verification and adversarial audit of Todorcevic--Tyros,
*A Dual Ramsey Theorem for Trees* (arXiv:2207.14599v1).

The self-contained author-facing discussion of the Lemma 27 Q issue is
[notes/lemma27_Q_counterexample.tex](notes/lemma27_Q_counterexample.tex).
It treats the extra starred mixed-product condition of Definition 20,
the reverse-lex frontier ordering, an arbitrary-height paper example,
and the distinction between an invalid Q construction and the
unrefuted Ramsey conclusion.

The project is a **statement-by-statement formalization**, not yet a
formal proof of the full dual-tree Ramsey theorem. The cumulative
[TeX audit](audit.tex) records verified statements, imprecisions,
counterexamples, and proposed repairs. `\ok` records a discharged
obligation; `\todo` marks a remaining gap or proposed change.

## Verified foundations

- Finite homogeneous trees, prefix order, the paper's executable
  skew / semi-complete / complete skew definitions, and variable words.
- Finite counterexamples to certain printed auxiliary-order and
  construction assertions, with explicitly scoped repair proposals.
- Support meet closure, uniqueness of directional immediate successors,
  maximal-interior signature boundaries and minimal outside-cut frontiers.
- The exact Lemma 27 frontier inequality `|R| <= d <= b^(m'+1)`
  (for positive branching and an early cut), via inverse-address
  prefix-antichain padding and a finite-level word count.
- An explicit collision-free `Fin d` coordinate map for literal
  signature markers, and the associated `D0/D2` coordinate partition.
- Cone-local auxiliary decoding, typed separation of original letters,
  auxiliary letters and genuine cone variables, root-aligned substitutions
  and corresponding span/refinement lemmas.
- The constructive canonical support map on a k-complete skew support:
  exact support rank along immediate successors, admissibility of every
  address in `b^{<k}`, an inverse address for every support vertex,
  bijectivity, and equivalence of the two prefix orders.
- Concrete canonical cone projections on **intrinsically safe tails**:
  `|I_T^{-1}(t)| + |z| < k`. Their roots, prefixes, rank increments,
  and inverse concatenation coordinates are all verified.
- The actual Lemma 27 Q-support skeleton has its expected cardinality
  and interior, is rooted and ambient meet-closed, has exactly 0 or b
  immediate successors at each vertex, and satisfies skew clause (iv).
  None of these facts alone establishes semi-complete skewness.
- A **kernel-checked source-facing counterexample** to the displayed
  Q leaf replacement, including the paper's Definition 20 starred-domain
  constraint: independent D2 bullet depths, in the actual reverse-lex
  ordered coordinates of a typed binary height-three example, produce
  new Q nodes at the same intrinsic height but with reversed
  lex/ambient-length order. In particular `condIIB(S_w) = false`,
  and the tree is not semi-complete skew. See
  `QLengthActualSkewFailure.lean`,
  `QLengthStarredDomain.lean`, and
  `QLengthStarredCoordinateOrder.lean`.
  The standalone author note proves the same obstruction for arbitrary
  complete-tree height n >= 3. This refutes the claimed unrestricted
  well-definedness of Q, not the final Ramsey existence theorem.

These are Lean theorems, not assumed lemmas. The main branch already
audits **546 source-facing declarations** for transitive
uses of unproved or nonstandard axioms. The authoritative count is
maintained in the CI workflow and increases with new checked results.
The complete theorem and the full construction of Lemma 27 are
**not** marked verified.

## Main remaining work

The leading obstacle remains the printed Lemma 27 reconstruction and its
mixed-product colouring. The geometric portion of its reconstructed tree
is extensively verified, but a genuine **small-height failure of skew
clause (ii)** has now been formalised for the actual Q map.

1. **Repair the Q tree component:** independently selected D2 bullet
   points can produce leaves of equal intrinsic Q-height but incompatible
   ambient lengths. Test a restriction aligning the projected terminal
   points to a common intrinsic level in the enclosing complete support,
   or another local correction; verify compatibility with the Ramsey
   subspace and colouring pullback. No repair is yet certified.
2. **Correct cone domains and bounds:** the source uses longer tails
   than the canonical map permits for some frontier heights. The
   shortened common domain and an extra-complete-level conversion
   have been verified at the type/geometry level, not yet with
   the numerical recursive bounds.
3. **Construct the full Q word:** the coordinate words, root-aligned
   substitution into the old word, smoothness/colouring compatibility,
   and invariance of the required variable fibres remain to be proved.
4. **Finish the Ramsey induction:** Lemma 28, Theorem 25, the recursive
   inequalities, and the full dual-tree theorem still need proofs.

The typed counterexample is for complete height three. It has not
been extended to the full large-parameter hypothesis package of
Lemma 27; the statement of the theorem itself is not marked false.

The source's **printed auxiliary linear order is not preserved** by
its claimed canonical embedding in general; this has a separate
kernel-checked counterexample. The prefix-tree isomorphism proved here
does not silently repair that auxiliary order.

## Reproducing verification

The Lean toolchain and Mathlib/dependency versions are pinned by
`lean-toolchain` and `lakefile.toml`. In a configured Lean workspace:

```sh
lake update
lake exe cache get
lake build
python3 scripts/check-skew-meet.py
python3 scripts/check-audit-tex.py
lake env lean scripts/CheckDualTree.lean > dualtree-axioms.log 2>&1
EXPECTED=$(grep -oE 'dualtree-axioms.log [0-9]+ \|\|' .github/workflows/lean.yml | awk '{print $2}')
python3 scripts/check-axiom-log.py dualtree-axioms.log "$EXPECTED"
```

The CI workflow in `.github/workflows/lean.yml` repeats these checks
and rejects `sorryAx` or unexpected proof axioms. The expected audit
count changes whenever verified endpoints are added.

## Navigation

`DualTree.lean` imports the full development. The main current
construction is in `CompleteSupportRoot.lean`,
`ImmediateSupportHeight.lean`, `CompleteSupportAddresses.lean`,
`CanonicalSupportInjective.lean`, `SupportReachability.lean`,
`CompleteSupportSurjective.lean`, `CanonicalSupportPrefixIso.lean`,
and `CanonicalConeCoordinates.lean` under `DualTree/`.
The counting/coordinate work is in `FrontierCardinality.lean`,
`LiteralMarkerCoordinates.lean`, and `BulletCoordinateRange.lean`.
The actual cone-word decoding bridge is in `CanonicalConeWordTransport.lean`.
The TeX audit is intentionally cumulative: older partial TODOs should
be read together with later validation entries.
