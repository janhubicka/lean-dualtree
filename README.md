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
- The forward-corrected actual Lemma 27 Q-support skeleton has its
  expected cardinality and **exact original interior**, is rooted and
  ambient meet-closed, has exactly 0 or b immediate successors at
  every vertex, and satisfies skew clause (iv).
- The corrected Q reconstruction preserves intrinsic ranks of old
  interior vertices, identifies exact Q ranks for both literal marker
  families, and verifies the old/old and both mixed old/new skew
  order clauses (ii) and (iii).
- The **two-band frontier rank matching theorem** is checked for every
  actual selected D2 projection P_i and its sorted ambient T-frontier f_i:
  (h_Q(P_i), h_T(f_i)) is either (h_S(cut), h_T(cut)) or
  (h_S(cut)+1, h_T(cut)+1), independent of local marked-point tails.
  This gives exact equivalences of strict and equal new/new intrinsic
  Q ranks with ambient T-frontier ranks.
- The conditional proof that the *whole Q support* is semi-complete
  skew when the selected D2 marked-point lengths are nondecreasing
  in sorted index order is proposed in PR #213 and **not yet part of
  verified main**. An explicit order-reflecting vector-one-complete
  D2 certificate is available as a source-facing proof interface,
  but still needs to be constructed from every printed W_* input.
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
audits **832 source-facing declarations** for transitive
uses of unproved or nonstandard axioms. The authoritative count is
maintained in the CI workflow and increases with new checked results.
The complete theorem and the full construction of Lemma 27 are
**not** marked verified.

## Main remaining work

The printed length-first reverse-lex leaf replacement has a
**kernel-checked failure** of skew clause (ii), even under the extra
starred mixed-product restriction. That remains distinct from the
proposed consistent **forward-lex repair**. For the repaired
construction the root, interior, branching, marker ranks, ambient
frontier bands and mixed old/new inequalities have passed Lean CI.

1. **Complete the conditional Q geometric repair:** verify PR #213,
   which combines the two-band matching with sorted D2 tail-length
   monotonicity to prove full semi-completeness of the *actual* Q
   support. This is a different statement from unrestricted
   well-definedness of the printed construction.
2. **Connect the actual W_* domain:** show that every relevant
   Definition 20 starred input yields the selected D2 order certificate,
   rather than assuming marked-point lengths are sorted for arbitrary
   mixed-product elements.
3. **Correct cone domains and quantitative bounds:** the verified
   common safe domain is b^{<k-(m+1)}; alternatively an extra complete
   level permits the original longer tails. The manuscript's numerical
   recursion and mixed Hales--Jewett parameters still need reconciliation.
4. **Construct the full Q word:** define g_w using actual cone words,
   typed original/auxiliary/cone-variable decoding and root-aligned
   substitution. Prove variable fibres, starredness and smooth
   colouring pullback. Current geometric proofs do not imply this.
5. **Finish the Ramsey induction:** Lemma 28, Theorem 25, the required
   recursive inequalities and the final dual-tree theorem remain open.

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
python3 scripts/check-q-stretched-forward.py
python3 scripts/check-q-arbitrary-source.py
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
The repaired source-facing Q construction and geometry occupy the
`ForwardSourceQTree`, `ForwardQInteriorExact`,
`ForwardQSkewIV`, `ForwardQExceptionalRanks`,
`ForwardQMarkerRankBand`, `ForwardQFrontierBandMatch`,
and `ForwardQAmbientRankClosure` modules.
The conditional full support proof under the selected starred D2
order is in the still-pending
`ForwardQCertifiedSemiComplete` module (PR #213).
The TeX audit is intentionally cumulative: older partial TODOs should
be read together with later validation entries.
