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
- The *actual forward-corrected Q support* has been proved
  **semi-complete skew**, conditional on the explicit selected D2
  marked-point length monotonicity (PR #213, merged and CI-audited).
  An order-reflecting vector-one-complete D2 certificate suffices.
  Constructing that certificate from every printed W_* input is
  an independent, still-open source-domain obligation.
- Under an explicit ambient T-bound and the proved Q geometric
  condition, the old source variable word gives a well-typed
  **placeholder** starred word on the actual Q support (PR #214).
  This does not yet construct the prescribed mixed-cone word g_w.
- The actual corrected forward D₀/D₂ starred input subtype has a
  canonical selected D₂ order with vector-one-complete marked-point
  lengths, and the real Q support is semi-complete skew on that subtype.
- The projected marked cones are disjoint and avoid the retained old
  variable roots; root-aligned local cone words can be patched into
  a genuine starred word on Q. A three-way raw-symbol decoder
  (original letters, auxiliary letters and cone variables) has
  a verified pointwise and evaluated semantics, including uniform
  variable fibres (merged PRs #225, #226, #228).
- Inside-cone changes to the coordinate words preserve the corrected
  starred domain and Q support and are Gamma₂-smooth-related
  (merged PR #229). A colouring on the corrected starred subtype
  extends to a total smooth colouring **exactly when** it is
  already constant on its starred smoothness classes (PR #230).
- The converse smoothness theorem identifies **all** corrected-starred
  Gamma₂-smooth comparisons as marked-cone patches: every related
  starred pair is recovered exactly by replacing the first input's
  bullet words inside its fixed marked cones with those of the second.
  Consequently smoothness of a starred colouring is **equivalent**
  to invariance under every such patch. The induced colouring
  \(c\circ Q\) still needs this invariance proved for its specific
  decoder and source colouring; support invariance by itself is
  insufficient (pending PR, Lean CI required).
- Fixing one alphabet letter gives a canonical representative for each
  Gamma₂ smoothness class of the **corrected** starred subtype: overwrite
  every marked-cone word with that letter, keeping points and outside
  symbols. This normalization is idempotent, and two inputs are related
  exactly when their normalizations agree. Consequently every colouring
  precomposed with normalization is smooth. **Important:** doing so may
  destroy the specific Q decoding or mixed-word span/surjectivity needed
  for Lemma 27; those properties remain unproved (PR #233, verified).
- **Definition 21 uses an existential Gamma₁/Gamma₂ partition** of
  the selected D₂ coordinates. The earlier all-Gamma₂ patch
  normalization treats only one special split, and should not
  be imposed on the full Lemma 27 colouring pullback. An arbitrary
  split now has its own corrected-starred compatibility/total-extension
  interface, and a binary one-bullet witness proves that some
  genuinely smooth word-dependent colourings fail the all-Gamma₂
  criterion. The arbitrary-partition extension criterion passed CI in PR #236;
  transporting the original simple-colouring B₁/B₂ witness to
  the selected frontier split remains open.
- The normalization map is additionally **provably non-surjective**
  on any inhabited corrected-starred domain with a selected D₂
  coordinate and two alphabet letters: every normalized input has
  the fixed letter at each marked point, while a genuine corrected
  starred input can be patched to have a different letter there.
  The Q tree is unaffected. This precisely obstructs treating
  normalization as a lossless reparameterization of the full
  mixed-product domain (verified in merged PR #235).
- A kernel-checked binary witness demonstrates that simply reordering
  the *same* marked-point assignment from the paper's reverse-lex
  frontier order to the corrected forward order can destroy
  vector-one-completeness (PR #227). Thus the old printed W_* domain
  is not automatically transported by a change of tie-break order.
- For any partition of the **literal corrected signature-marker set** R,
  the actual bijection between R and the forward-sorted selected D₂
  frontier indices defines a Gamma₁/Gamma₂ split. The marked
  Gamma₁ words are identical; Gamma₂ marked points, outside-cone
  letters and projected Q nodes are preserved under smoothness.
  **Open:** construct the canonical address transport from the paper's
  abstract simplicity marker set A to R and transfer B₁/B₂ (new Lean module,
  pending CI).
- A separate **full-frontier Q word interface** now patches one
  root-aligned local symbol map at every sorted complete-support
  outside-cut frontier coordinate (D₀ and D₂), not just inside
  D₂ projected marked-point cones. Its selector, root preservation,
  inside/outside word semantics, conditional starred output on the
  actual Q tree and independence from marked points for fixed local
  maps are subject to Lean CI (follow-up PR).
  The specific paper decoder and colouring compatibility remain open.
- The full-frontier three-constructor interface now conditionally
  assembles and evaluates typed raw cone words at EVERY corrected
  sorted D₀/D₂ frontier: original letters remain constants, auxiliary
  letters use a typed per-frontier decoder, and genuine cone variables
  are uniformly mapped to old source roots. Local root alignment is
  explicit and the global decoded word has exact corrected Q support.
  The prescribed paper-specific local words and image/refinement
  properties remain unproved (merged PR #239 verifies the conditional interface).
- At each genuine forward-sorted frontier, an explicit auxiliary
  decoder `R_i` from m+1 symbols now targets only the *actual
  visible old source variable roots* (proper support predecessors).
  The forward frontier rank bound supplies its numerical domain,
  and masking irrelevant raw symbols outside the cone makes the
  required auxiliary root alignment automatic. Genuine cone-variable
  root transport remains an independent premise. This source-facing
  decoder and its evaluated Q-word statement passed CI in merged
  PR #240 (980 transitive theorem endpoints).
- A new necessary-and-sufficient **cone-variable-root visibility**
  criterion identifies the remaining transport obligation: a local
  cone-variable occurrence above frontier f_i can map to an original
  source variable v exactly when v's root is a strict ancestor of f_i.
  Thus the root must belong to the concrete visible ancestor list V_i;
  if V_i is empty no genuine variable can occur in that cone. In
  particular the canonical cone projection P_i(r) of a local variable
  root r is generally **not itself** an allowable old variable root.
  The finite visibility certificate replaces an arbitrary prefix
  premise, but variable identifications may reduce the Ramsey span
  (8 verified source-facing endpoints, merged PR #241).
- A finite **visible-root capacity** result makes the outstanding
  cone-variable transport quantitative. The actual list V_i of old
  variable roots strictly preceding a frontier is duplicate-free,
  has length at most m+1, and is in canonical bijection with the
  corresponding source-variable subtype; the corrected R_i decoder
  covers each of these ACTUAL variables. Consequently if m+2
  different local variable symbols all occur in one frontier cone,
  any root-aligned transport must identify at least two names.
  This is a conditional obstruction to *injective* local-variable
  transport, not a refutation of the Ramsey theorem (9 verified source-facing
  Lean endpoints, merged PR #242).
- Under the exact requirement that no genuine local variable occur
  in a frontier cone without any visible old source root, a fully
  explicit *first-visible-root* assignment now constructs a legal
  three-way starred Q word with the checked auxiliary R_i decoder.
  Conversely the visibility theorem makes the condition necessary:
  it is an iff for mere root-aligned transport existence. This
  canonical root choice deliberately maps ALL local variable names
  in each cone to the same old root, so cannot on its own establish
  the original independent-variable span (6 CI-certified endpoints,
  merged PR #243).
- The **actual mixed-product coordinate words** are now sampled
  through the certified forward canonical cone projection. The
  inverse-address equation proves that removing the frontier prefix
  from P_i(z) recovers exactly z, so a concrete local letter
  interpolation L_i satisfies L_i(P_i(z)) = x.words i z for every
  forward-sorted D₀/D₂ coordinate. Using these original-letter
  symbols gives a legal starred Q word on the actual Q support.
  Auxiliary and genuine local variable symbols are not yet part
  of this concrete interpolation (7 proposed Lean endpoints,
  pending CI).
- Definition 21's **general** Gamma₁/Gamma₂ smoothness relation now
  has a verified exact observable characterization in ACTUAL corrected
  Q outputs: at every fixed canonical projected position P_i(z),
  words agree on D₀ and Gamma₁, and on Gamma₂ outside the
  selected marked cone; the Gamma₂ projected marked points also
  agree. Conversely these observed Q-word/point equalities
  recover the input SmoothRelated comparison because the canonical
  projection reflects equality of local tails. Gamma₁ marked points
  need not agree and full Q trees need not coincide. The exact pointwise equality between actual Q output symbols
  and these typed original coordinate letters is checked separately,
  avoiding arbitrary universe choices for the empty local-variable
  type. This is the interface for proving colouring-factorization of the specific
  Definition 24 simple colouring (10 new Lean endpoints; pending CI).
- **Every actual selected D₂ frontier has an old visible source variable.**
  The genuine original source root is an interior variable and strictly
  precedes the sorted frontier of each literal D₂ signature marker,
  so its checked visible-root list is nonempty and the explicit
  R_i decoder reaches that root. In particular a raw local family
  whose genuine cone-variable occurrences are confined to D₂
  frontiers admits the verified first-visible-root assignment and
  constructs a legal starred Q word. This does NOT establish the
  same for arbitrary D₀ frontiers or preserve independent local
  variable names (8 CI-verified endpoints in merged PR #246).
- A canonical **Gamma₁/Gamma₂ observable fingerprint** now retains
  entire D₀/Gamma₁ words, masks inside-cone letters on Gamma₂, and
  keeps only Gamma₂ marked points (Gamma₁ marked points may move).
  The exact source-facing target is fingerprint(x)=fingerprint(y)
  iff SmoothRelated(gamma1,x,y). Every smooth colouring of the
  genuine corrected starred domain then factors through this
  explicit record, with a total factor map on unrepresented
  fingerprints supplied by a fallback colour. This is a quotient
  normal form, NOT proof of the paper's specific simple-colouring
  factorization or its variable-word span (10 CI-verified endpoints in merged PR #247).
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
audits **1039 source-facing declarations** for transitive
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

1. **Relate the printed and repaired W_* domains:** the naive
   reverse-to-forward frontier permutation is refuted by the typed
   vector-one-completeness counterexample. Any corrected proof must
   transport/reassign cone words and marked points together or
   establish a new source-domain Ramsey lemma compatible with the
   forward-sorted selected D₂ order.
2. **Correct cone domains and quantitative bounds:** the verified
   common safe domain is b^{<k-(m+1)}; alternatively an extra complete
   level permits the original longer tails. The manuscript's numerical
   recursion and mixed Hales--Jewett parameters still need reconciliation.
3. **Identify the paper's particular Q word and colouring:** the
   general root-aligned three-way decoder and its evaluated semantics
   are verified. It remains to instantiate its *specific* raw cone
   words, auxiliary decoder and variable-root transport from Lemma 27,
   prove their alignment and fibre properties, and demonstrate
   classwise compatibility of the actual induced colouring c ∘ Q.
   General smooth extension works for an arbitrary Gamma₁/Gamma₂
   split, but the particular B₁/B₂-to-Gamma transport and
   classwise compatibility are not automatic.
4. **Finish the particular full-frontier Q decoding:** the
   corrected all-frontier patcher and three-constructor evaluation
   are checked. The proposed genuine visible-ancestor R_i decoder
   now discharges the auxiliary alignment step (verified in #240).
   Existence of some aligned cone-variable root assignment has a
   proposed exact visible-nonemptiness characterization, but the
   canonical construction collapses names. The paper's specific
   local raw words, a faithful source-root transport, source
   signature and span/refinement preservation remain open. The older marked-point-cone
   interface is distinct.
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
The author-facing proposed geometric proof is
[notes/corrected_forward_Q_geometry.tex](notes/corrected_forward_Q_geometry.tex).
The repaired source-facing Q construction and geometry occupy the
`ForwardSourceQTree`, `ForwardQInteriorExact`,
`ForwardQSkewIV`, `ForwardQExceptionalRanks`,
`ForwardQMarkerRankBand`, `ForwardQFrontierBandMatch`,
and `ForwardQAmbientRankClosure` modules.
The conditional full support proof under selected D2 length order
is verified in `ForwardQCertifiedSemiComplete` (merged PR #213).
`ForwardQRetainedWordScaffold` isolates boundedness and old roots.
`ForwardQDisjointWordCones`, `ForwardQLocalWordPatching`,
`ForwardQThreeWayConeWordAssembly` and
`ForwardQThreeWayEvaluation` supply conditional word assembly and
its exact evaluation. `ForwardQStarredSmoothConePatches` and
`ForwardQStarredSmoothExtension` isolate the remaining
smooth-colouring compatibility obligation.
`ForwardQStarredPatchCriterion` supplies its exact marked-cone-patch
normal form and the universal output-map diagnostic.
`ForwardQStarredNormalization` supplies canonical smoothness-class
representatives for the all-Gamma₂ special case; its effect on the
required Ramsey span remains open. `ForwardQStarredSmoothPartitions`
handles the paper's existential Gamma₁/Gamma₂ split.
`ForwardQMarkerSmoothPartition` transports literal signature-marker
splits to genuine corrected D₂ Gamma₁/Gamma₂ coordinates.
`ForwardQFullFrontierWord` supplies conditional word patching on all
outside-cut complete-support frontiers, not just marked-point cones.
`ForwardQFullFrontierThreeWay` supplies a conditional three-constructor
decoder and exact evaluated semantics on those full frontier cones.
`ForwardQVisibleAncestorDecoder` constructs the CI-verified concrete
per-frontier R_i using genuinely visible typed source variables.
`ForwardQConeVariableVisibility` characterizes the necessary and sufficient
per-occurrence condition for genuine cone-variable root transport.
`ForwardQVisibleRootCapacity` bounds its number of distinct old-root targets,
gives faithful finite indices and establishes the m+2 versus m+1
non-injectivity obstruction.
`ForwardQCanonicalConeRootChoice` supplies the verified iff criterion
for existence of some old-root transport and a deliberately collapsing
first-visible-root witness.
`ForwardQActualCoordinateWord` samples genuine input coordinate letters
at corrected canonical projected positions across all D₀/D₂ frontiers.
`ForwardQProjectedSmoothObservables` characterizes arbitrary Gamma₁/Gamma₂
smoothness by exactly the corresponding observable genuine Q symbols
and fixed Gamma₂ projected nodes.
`ForwardQObservableFingerprint` constructs an explicit quotient record,
whose equality characterizes the same relation and through which
smooth starred colourings factor.
`ForwardQBulletRootVisibility` establishes nonempty old variable roots at all
actual D₂ frontiers, without inferring the same property for D₀.
`ForwardQStarredOrderReindexObstruction` records the verified
failure of naive printed-to-repaired starred input reindexing.
The TeX audit is intentionally cumulative: older partial TODOs should
be read together with later validation entries.
