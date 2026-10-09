# lean-dualtree

Lean 4 verification and adversarial audit of Todorcevic--Tyros,
*A Dual Ramsey Theorem for Trees* (arXiv:2207.14599v1).

The project is a **statement-by-statement formalization**, not yet a
formal proof of the full dual-tree Ramsey theorem. The cumulative
[TeX audit](audit.tex) records verified statements, imprecisions,
counterexamples, and proposed repairs. `\\ok` records a discharged
obligation; `\\todo` marks a remaining gap or proposed change.

## Verified foundations

- Finite homogeneous trees, prefix order, the paper's executable
  skew / semi-complete / complete skew definitions, and variable words.
- Finite counterexamples to certain printed auxiliary-order and
  construction assertions, with explicitly scoped repair proposals.
- Support meet closure, uniqueness of directional immediate successors,
  maximal-interior signature boundaries and minimal outside-cut frontiers.
- Injectivity of the literal signature-marker-to-frontier map, giving
  `|R| <= d` and the partition `d = d0 + d2`.
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

These are Lean theorems, not assumed lemmas. As of the latest merged
code, CI audits **319 source-facing declarations** for transitive
uses of unproved or nonstandard axioms. The complete theorem and the
full construction of Lemma 27 are **not** marked verified.

## Main remaining work

The leading obstacle is the printed Lemma 27 reconstruction and its
mixed-product colouring. In particular:

1. The source uses longer ambient cone tails than the intrinsic
   canonical map permits. Their domain and the recursive mixed-product
   dimension must be repaired together.
2. The frontier bound `d <= b^(m'+1)` requires finishing the finite
   antichain-counting argument; the general padding reduction is under
   development.
3. The global code `Q`, its well-typed cone-variable substitution,
   and constancy of the induced colouring on smoothness classes still
   need to be constructed and proved.
4. Lemma 28, Theorem 25, the stated recursive bounds, and the final
   dual-tree theorem still require their own Lean proofs.

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
python3 scripts/check-axiom-log.py dualtree-axioms.log 319
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
The TeX audit is intentionally cumulative: older partial TODOs should
be read together with later validation entries.
