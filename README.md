# lean-dualtree

**Current verified status (17 October 2026; main through PR #345).**
The full Lean build, finite regression suite, static source audit, and curated
transitive-axiom audit pass on main with **1,520 distinct selected endpoints**
and no `sorryAx`. This endpoint count is not a theorem-completion percentage.

The corrected Q construction, the full first-l model geometry and canonical
selector on actual Q outputs, the exact final rank-budgeted support T'_M,
the intrinsic rank formula, and all-vertex directional EXISTENCE are validated.
Projected immediate-child classification, direction reflection, and projected
parent AT-MOST-ONE direction are now checked. Retained-parent uniqueness is
the new PR #346 and remains CI-pending on its refreshed head.

The published semi-complete I_U/reverse auxiliary W_* alignment, complete
skew ordering and leaf-height clauses of T'_M, the global ambient word f',
its Q-span containment, and the final Ramsey induction remain OPEN.
These are mathematical proof obligations, not merely elaboration errors.

Historic notes below record the status at their time; earlier "CI pending"
markers remain historical. The [adversarial library audit](notes/adversarial_library_audit_20261015.md)
and `scripts/audit-lean-library.py` document trust and import-graph coverage.

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


- **B2-empty simplicity-to-smoothness (merged #262, CI verified):** for the genuine
  corrected ambient-fibrewise Q, equality of all enlarged coordinate words
  implies equality of its complete root-labelled output words even if D2 marked points
  move; the Q interior stays equal to the old source interior. Therefore a
  Definition 24 simple colouring with the special witness B2 = empty pulls
  back to a Gamma1-all smooth colouring, with a classwise total extension
  to the enlarged mixed product. This does NOT transfer a general B2 witness
  or complete the final Ramsey step. See
  `DualTree/ForwardQSimpleLetterSmooth.lean` (eight audited endpoints).

- **Full original f-fibre Q observability (six new endpoints, CI pending):**
  for any Gamma1/Gamma2 split, smoothness fixes enlarged-alphabet
  letters on the observable D0, Gamma1 and Gamma2-outside-cone
  coordinates. Their decoded Q symbols agree throughout the WHOLE
  corresponding original ambient f-variable fibre. Gamma2 also
  preserves the projected Q marked node. This is not a proof of
  full arbitrary-B2 simplicity without root coverage and A-to-R
  marker transport. See `ForwardQAmbientFibreSmoothObservable.lean`.

- **Forward-complete prefix isomorphism (new, CI pending):** the genuine
  corrected canonical support embedding I_T both preserves and reflects
  ambient prefixes, and its inverse addresses preserve/reflect prefixes.
  This gives an exact geometric bridge between marked cones and intrinsic
  source addresses without using the false printed reverse-lex order.
  See `DualTree/ForwardCompletePrefixIso.lean` (four new theorems).

- **Exact safe frontier-cone coverage (CI pending):** every actual
  T-support descendant of a corrected forward-sorted frontier whose
  intrinsic rank difference fits the safe common tail height
  `k-(m+1)` is exactly `P_i(z)` for its unique canonical suffix `z`.
  The inverse-address decomposition and injectivity of the common cone
  projection are also proved. Out-of-budget roots use the distinct Q
  fallback case and are NOT claimed to belong to this local image.
  See `DualTree/ForwardInverseConeTails.lean` (eight audited theorems). This also proves that ambient
  exclusion from a genuine projected Q marked cone forces the recovered
  local address to lie outside its selected D2 marked cone.

- **Safe whole-fibre smoothness (two new endpoints, CI pending):**
  if a real ambient f-variable root is a safe descendant of frontier i
  and outside every Gamma2 projected Q marked cone, its recovered local
  suffix is an observable coordinate. Smoothness of two actual enlarged
  mixed inputs then gives equal full Q output words on EVERY occurrence
  of that f-variable. This combines real root coverage with the merged
  fibrewise Q(iv) theorem; default/out-of-safe cases and the abstract
  Definition 24 A-to-R marker correspondence remain open.
  See `DualTree/ForwardQSafeFibreSmoothness.lean`.

- **Whole ambient-fibre default cases (8 endpoints, CI pending):**
  original f-constants, variables rooted at/before the cut, late roots
  with no selected frontier, and post-cut roots whose canonical T-inverse
  tail is beyond the shortened safe mixed-product domain all give
  input-independent Q letters. These cases are packaged in
  `DefaultFibre`; actual starred Q outputs agree at every such
  position without any smoothness assumption. Together with the
  already verified safe-root Gamma2-exterior transport, this reduces
  general Q smoothness to a complete fibre-by-fibre partition and
  Definition 24's A-to-R marker correspondence. See
  `DualTree/ForwardQFibreDefaults.lean`.

- **Complete Gamma2-exterior Q word equality (6 new endpoints, CI pending):**
  the actual corrected fibrewise decoder is compared on EVERY ambient
  original f-position by exhausting constants, early roots, absent
  frontiers, unsafe tails, and safe roots. For safe roots, the
  inverse-tail length equals the intrinsic T-rank difference,
  so the verified safe-exterior lemma applies. Thus two smooth-related
  enlarged mixed inputs have identical finished Q output symbols
  wherever the original f-variable root is outside the selected
  Gamma2 Q marked-point cones. No ambient-occurrence cone test or
  Hall assignment is assumed. The source-facing comparison now also holds at all AMBIENT positions
  outside actual Gamma2 marked successor cones: original f-roots prefix
  every occurrence, so ambient exclusion implies root exclusion.
  Together with equal interiors and fixed Gamma2 marked projections,
  this proves all three corrected R-indexed simplicity observables.
  Definition 24 canonical A-to-R identification and the
  final mixed-product Ramsey refinement are still open.
  See `DualTree/ForwardQAllExteriorFibres.lean`.

- **Definition 24 canonical-marker transport interface (2 endpoints, CI pending):**
  the proof of the corrected Q simplicity observables is now factored
  from the one remaining canonical identification. Given an explicit
  equivalence from the paper's model boundary A to the actual selected
  D2 indices, a matching B2/Gamma2 partition, and the identity
  `I_{Q(w)}(a) = P_{e(a)}(s_{e(a)}(w))`, a genuinely Definition 24-style
  simple colouring pulls back to a smooth colouring. The existing
  classwise-extension theorem then provides a total smooth colouring
  of the entire enlarged mixed product. The canonical A-to-R
  identification remains a necessary, UNPROVED hypothesis.
  See `DualTree/ForwardQMarkerTransportInterface.lean`.

- **All corrected Q leaves are literal signature markers (five new endpoints,
  CI pending):** an actual Q terminal is exactly the projection of one
  selected D2 coordinate, and different D2 indices give different leaves.
  Consequently the fixed literal signature marker set R is in a canonical
  bijection with the terminal vertices of EACH reconstructed corrected
  Q tree. Its value at r is the original projected point
  `P_(index r)(s_(index r))`, which lies below r in the ambient
  prefix order. This reduces the remaining Definition 24 boundary issue
  to identifying the canonical model A with the Q leaves; existence of
  that A-to-R identification is NOT asserted.
  See `DualTree/ForwardQLiteralMarkerLeafEquiv.lean`.

- **Literal-R canonical terminal and R-simple pullback (four endpoints,
  CI pending):** for any starred output U, select a terminal above
  an actual corrected first-exit marker r if one exists. For EVERY
  genuine corrected Q(w), the selected terminal is UNIQUE and
  exactly P_(index r)(s_(index r)). Consequently the abstract
  canonical-marker transport hypothesis is now DISCHARGED for the
  source-relative marker set R: an R-simple colouring pulls back
  to a smooth colouring and extends to a TOTAL smooth colouring
  of the entire enlarged mixed product. This is not a proof that
  a colouring simple relative to Definition 24's canonical model
  boundary A is necessarily R-simple. The remaining A-to-R
  address/direction identification must still be proved.
  See `DualTree/ForwardQRelativeMarkerSelector.lean`.

- **Arithmetic first-l model boundary (7 theorems, CI pending):**
  define the b-ary heap address `index(∅)=0`,
  `index(s⌢i)=b·index(s)+1+i`, to encode forward breadth-first
  positions. For b>0, the candidate first-l model interior
  `H_l={s:index(s)<l}` is ambient prefix-closed, and its external
  immediate-child boundary `A_l` is an antichain whose indices lie
  in `[l,b·l]`. This gives an explicit arithmetic model for the
  A side of the remaining canonical correspondence. The equivalence
  of this numbering with the CORRECTED forward auxiliary order,
  and the direction-preserving A-to-R map, still require proof.
  See `DualTree/ForwardModelBoundaryHeap.lean`.

- **Exact model boundary interval (2 new endpoints, CI pending):**
  for l>0 the forward heap candidate has the exact boundary
  `A_l = {s : l ≤ heapIndex(s) ≤ b·l}`. The converse to the
  previous numeric bound and the finite regression for b=1–4,
  l=1–29 are in `ForwardModelBoundaryInterval.lean` and
  `scripts/check-model-boundary-heap.py`. The identification with
  corrected forward shortlex and the canonical A-to-R direction
  transport remain open.

- **Forward model child-order blocks (3 endpoints, CI pending):**
  siblings are ordered by their direction, while all children
  of an earlier heap-index parent precede all children of a later
  parent. This is the direction-aware arithmetic input needed to
  transport model boundary A to corrected literal R, not yet a
  proof of the full heap/ForwardAux order isomorphism.
  See `DualTree/ForwardModelHeapChildOrder.lean`.

- **Finite ambient height for model boundary (3 endpoints, CI pending):**
  every node has length at most its heap index. Thus the first-l
  model interior fits in `b^{<n}` when `l≤n`, and the complete
  external model boundary fits when `b·l<n`. This is a convenient
  explicit bound for transporting Definition 24's FINITE canonical
  boundary into the unbounded arithmetic model; it is not yet the
  direction-preserving A-to-R correspondence.
  See `DualTree/ForwardModelBoundaryHeight.lean`.

- **Equal-level forward lex order and heap index (4 new endpoints,
  CI pending):** strict comparison of heap-indexed parents persists
  under arbitrary equal-length suffixes. Ordinary forward lex order
  on equal-length addresses implies nondecreasing heap index;
  conversely strictly ordered heap indices on one level imply
  forward lex order. This is a step toward the corrected
  ForwardAux order-isomorphism; distinct levels, index bijectivity
  and canonical model A-to-literal-R transport remain open.
  See `DualTree/ForwardModelHeapLexOrder.lean`.

- **Forward model heap levels (6 endpoints, CI pending):** exact
  numerical min/max bands are defined for all tree depths, with
  `max(b,n)+1=min(b,n+1)`. Every length-n address lies in its
  level band, and positive branching makes shorter addresses have
  strictly smaller heap indices. Combined with equal-level lex
  monotonicity, the heap index is now proved MONOTONE for the
  corrected length-first forward auxiliary order. Full order
  reflection/injectivity and the canonical A-to-R address map
  remain open. See `DualTree/ForwardModelHeapLevels.lean`.

- **Arithmetic model forward-order isomorphism onto its image
  (2 endpoints, CI pending):** every positive-arity b-ary heap index
  uniquely determines its finite direction sequence. Combined with
  the already checked heap level bands and same-level lex ordering,
  `ForwardAux s t ↔ heapIndex(s) ≤ heapIndex(t)`. This is the exact
  arithmetic correction of the printed REVERSE-lex convention on
  the homogeneous model. Surjectivity of heap coding onto Nat and
  the canonical model A-to-literal-R direction transport remain
  separate obligations. See `DualTree/ForwardModelHeapInjective.lean`.

- **Surjective model heap enumeration (four endpoints, CI pending):**
  strong induction on an index k+1 constructs a parent word of index
  k/b and attaches direction k%b. Together with heap injectivity,
  this gives an explicit equivalence `Node b ≃ Nat` for positive b.
  The first-l arithmetic model interior is now canonically equivalent
  to `Fin l` and has exactly l elements. This completes the
  homogeneous forward-order arithmetic model. The map from its
  canonical boundary A to the literal R markers of arbitrary
  semi-complete skew sources remains open.
  See `DualTree/ForwardModelHeapSurjective.lean`.

- **Explicit finite model boundary enumeration (three endpoints, CI pending):**
  for positive b and l, the canonical forward model boundary
  A_l is indexed without choices by its contiguous heap interval
  [l, b*l]. Hence A_l is equivalent to Fin (b*l-l+1), and
  its cardinality is exactly b*l-l+1. The equivalence uses the
  corrected forward auxiliary order, not the false printed
  reverse-lex order. This is the model side only: a genuine
  direction-respecting boundary map A_l to source R is still open.
  See `DualTree/ForwardModelBoundaryEnumeration.lean`.

- **Fixed corrected-Q leaf direction incidence (two endpoints, CI pending):**
  at every original interior node s and every direction i, the
  genuine projected Q leaf P_r(x) lies in the cone of s++[i]
  exactly when the literal marker r lies there. In particular
  this direction incidence is independent of the selected
  mixed-product point x and its leaf depths. This advances the
  geometric model A-to-R transport without pretending to have
  constructed its full canonical address map or the final Ramsey
  refinement. See `DualTree/ForwardQMarkerDirectionalIncidence.lean`.

- **Fixed source-labelled Q vertex shape (four endpoints, CI pending):**
  define the disjoint union of the fixed old source interior with
  the literal source signature marker set R. Its realization in
  any actual corrected Q output sends interior nodes to themselves
  and marker r to the genuine projected terminal P_r(x). The map is
  bijective, so any two Q outputs have a canonical matching of their
  underlying vertices through a fixed type, without choosing an
  arbitrary permutation of leaves. Preservation of the rooted
  prefix/direction relations under this matching remains to prove;
  no full Definition 24 A-to-R transport is asserted.
  See `DualTree/ForwardQFixedVertexShape.lean`.

- **Fixed prefix-tree order of the actual corrected Q (two endpoints, CI pending):**
  on the already verified fixed vertex type `interior S ⊕ R`,
  define the input-independent relation: old-to-old means prefix;
  old-to-marker means strict prefix; a marker is never below an
  old vertex; and distinct markers are incomparable. The genuine
  realization in each Q(x) preserves and reflects this relation.
  Consequently all Q outputs have canonically identified PREFIX
  TREE SHAPES even when marked leaf depths vary. The remaining
  Definition 24 problem is the actual direction-labelled canonical
  first-l model address map and A-to-R correspondence. See
  `DualTree/ForwardQFixedPrefixIso.lean`.

- **Initial-segment theorem for actual source interior (five endpoints, CI pending):**
  for positive branching, a genuine source vertex is interior exactly
  when it precedes or equals the last interior cut in corrected
  ForwardAux. This follows from the full-before source witness and
  supplies a concrete directional successor for every earlier vertex.
  Hence the source interior is downward closed in forward order,
  and every later source vertex is a leaf. The first-l canonical
  **compressed address** identification and A-to-R marker transport
  still require separate theorems.
  See `DualTree/ForwardSourceInitialInterior.lean`.

- **Uniqueness of actual source cut-child leaves (six endpoints, CI pending):**
  for every direction i at the last source interior cut, the genuine
  uniquely chosen immediate successor is an actual SOURCE LEAF, lies in
  the cut++[i] cone, and is the ONLY source vertex in that cone.
  Distinct directions give distinct leaves. This gives the cut-child
  component of the source-leaf / literal-R correspondence without
  choosing an arbitrary leaf enumeration. The exceptional first-exit
  marker component and full first-l model boundary correspondence
  remain separate.
  See `DualTree/ForwardSourceCutLeaves.lean`.

- **Exceptional source-leaf first-exit markers are injective (five new endpoints, CI pending):**
  genuine exceptional terminals t outside the final cut cone map
  to their literal corrected first-exit markers r(t) in R.
  No two distinct source terminals have the same marker: their
  ambient meet would be an interior source vertex outside the final
  forward cut, contrary to the verified maximality condition.
  Conversely every actual signature-terminal marker has an
  exceptional-leaf preimage. Combined with #289 this isolates
  the two halves of the source leaf/R correspondence. The full
  A_l-to-R canonical direction-address map is still open.
  See `DualTree/ForwardSourceExceptionalMarkers.lean`.

- **Fixed direction-labelled corrected-Q transport (four new endpoints, CI pending):**
  for every old source interior node, every outgoing direction and every
  Q vertex, child-cone membership is the same as for its FIXED source
  label, independently of the mixed-product input and moving terminal
  depths. The canonical input-to-input vertex transport now preserves
  and reflects BOTH prefix order and every old-interior child cone.
  This supplies a genuine direction-labelled source-shape invariant.
  It does not yet produce the canonical model first-l address map,
  the A-to-R boundary equivalence, or the full Ramsey refinement.
  See `DualTree/ForwardQFixedDirectionIso.lean`.

- **Intrinsic Q rank on fixed source labels (three new endpoints, CI pending):**
  each old interior or literal R label has a source-defined intrinsic
  rank, counting its strict original-interior predecessors. The
  genuine corrected Q realization has exactly this rank for every
  mixed-product input, and the canonical vertex transport between Q
  outputs preserves it. These results, with the verified prefix and
  direction invariants, supply a common LEVELLED directed tree.
  The first-l model address map and A-to-R correspondence remain open.
  See `DualTree/ForwardQFixedRank.lean`.

- **Canonical admissible addresses for arbitrary semi-complete source trees (five new endpoints, CI pending):**
  the actual forward-skew source has a canonical admissible
  directional path from its root to each source vertex, with
  address length equal to intrinsic rank. The construction
  adapts the generic first-immediate-successor induction and
  unique direction property from the complete-support library
  without falsely assuming equal source leaf heights.
  The resulting realized address map is bijective.
  Identifying its interior addresses with the first l forward
  heap positions, and then transporting A_l to literal R,
  remains open. See `DualTree/ForwardSourceCanonicalAddresses.lean`.

- **Canonical source leaf / literal R marker equivalence (five new endpoints, CI pending):**
  every corrected literal R marker lies below exactly one original
  source leaf, and every original source leaf lies above exactly one
  literal R marker. The proofs combine the two marker families,
  source meet closure and the boundary antichain, without assuming
  an arbitrary leaf ordering. The resulting explicit type equivalence
  has prefix incidence as its characterizing invariant. This closes
  the source-leaf/R component, NOT the model A_l-to-leaf canonical
  address map or the Ramsey refinement. See
  `DualTree/ForwardSourceLeafMarkerEquiv.lean`.

- **Exact forward-order transport for source canonical addresses (six endpoints, CI pending):**
  the genuine semi-complete source walk preserves and reflects the
  corrected length-first forward auxiliary order on all admissible
  directional addresses, even when its support edges are stretched.
  The proof uses the existing generic lex walk monotonicity and
  source skew clauses (ii) and (iii). A concrete cut address is
  chosen by the verified source-address equivalence, and the
  original source interior is characterized as the admissible
  address initial segment ending at this cut address. The
  stronger equality with the full first-l HEAP initial segment
  still requires admissibility of all intermediate addresses.
  See `DualTree/ForwardSourceAddressOrder.lean`.

- **No missing homogeneous heap addresses before the source cut (five endpoints, CI pending):**
  a strong induction on b-ary heap index proves that EVERY ambient
  direction sequence no later than the canonical source cut address
  is admissible, not just those previously known to occur in the
  source. At each child, the parent is inside the already checked
  initial source interior, so its full directional branching supplies
  the missing successor. The resulting entire heap interval
  is exactly the realized source interior address set.
  Counting this interval against source interior cardinal l, and
  then constructing the A_l-to-source-leaf bijection, are next.
  See `DualTree/ForwardSourceHeapInitial.lean`.

- **Exact first-l canonical source interior (six endpoints, CI pending):**
  construct the canonical equivalence between the entire homogeneous
  initial heap interval ending at the source cut and the ORIGINAL source
  interior. Injectivity is directional-walk uniqueness; surjectivity
  is the full source address theorem and the cut-index bound.
  Compare the interval's verified cardinality with the source's
  stipulated l interior vertices to conclude
  `heapIndex(cutAddress)+1=l`. Thus the first l homogeneous heap
  addresses are EXACTLY the source interior addresses, without gaps.
  The model external boundary A_l to source-leaf/R correspondence
  is the remaining geometric bridge.
  See `DualTree/ForwardSourceInteriorFirstL.lean`.

- **Injective realization of the canonical model boundary (four new endpoints, CI pending):**
  every immediate child outside the first-l homogeneous interior
  is admissible in the original semi-complete source: its parent
  is interior and hence has all genuine directional successors.
  Its realized source vertex must be terminal because the address
  lies outside the interior. The resulting actual map from
  the model boundary A_l into the original source leaf set
  is injective by directional-walk uniqueness.
  Surjectivity, and therefore the final A_l-to-R equivalence,
  remains open. See `DualTree/ForwardSourceBoundaryLeaves.lean`.

- **Canonical model A_l-to-literal-R marker equivalence (four endpoints, CI pending):**
  every original source leaf has a nonempty canonical direction
  address; removing its last direction leaves an interior address,
  while the terminal address lies outside the first-l interior.
  This supplies surjectivity of the previously verified boundary
  realization, hence a genuine A_l ≃ SourceLeaf(S) equivalence.
  Composing with the already checked source-leaf/R equivalence
  produces A_l ≃ R without an arbitrary leaf order.
  The Definition 24 point-selector identity for actual corrected Q
  outputs, starred input-domain transport and final Ramsey induction
  remain open. See `DualTree/ForwardSourceBoundaryEquiv.lean`.

- **Model-A-indexed relative simplicity and smooth pullback (eight endpoints, CI pending):**
  use the verified corrected source equivalence A_l ≃ R ≃ D2
  to define a source-relative terminal observable for model
  boundary addresses a∈A_l on arbitrary starred outputs.
  On every ACTUAL corrected Q(w) it equals the genuine projected
  D2 marked point. Transport any B2⊆A_l to literal R,
  and apply the previously checked relative-R theorem to
  obtain smoothness and a TOTAL smooth extension of the
  induced colouring under this precise A-relative simplicity
  hypothesis. This does NOT identify that observable with
  Definition 24's published canonical I_U(a) for arbitrary U,
  or finish the mixed-product Ramsey refinement.
  See `DualTree/ForwardQModelBoundaryTransport.lean`.

- **Canonical model-leaf directional incidence (six endpoints, CI pending):**
  the corrected model boundary equivalence A_l ≃ SourceLeaf(S) ≃ R
  is shown to respect every outgoing direction at every original
  source interior vertex. The actual projected Q terminal in the
  corresponding D2 coordinate has precisely the same first-direction
  cone membership as the original source leaf, even when its
  ambient depth changes. This supplies the missing source-to-Q
  direction-incidence invariant for extending the published
  Definition 24 canonical selector. The published map I_U for
  arbitrary semi-complete starred U, and its zero-interior
  convention, still require a separate formal definition.
  See `DualTree/ForwardQModelLeafIncidence.lean`.

- **Canonical two-sorted model vertices of genuine Q (eight endpoints, CI pending):**
  combine the actual first-l homogeneous interior with its external
  boundary, then the checked interior/marker equivalences, to obtain
  a canonical address-labelled equivalence with every corrected Q
  vertex set. Interior addresses retain original source vertices;
  boundary addresses give the genuine selected D2 projected points.
  Across arbitrary corrected Q inputs this common labelling
  preserves and reflects all prefix comparisons, every old-interior
  outgoing cone, and intrinsic ranks. The final assertion that
  this agrees with the model's OWN prefix/direction structure,
  and with the published Definition 24 I_U on arbitrary U,
  is still open. See `DualTree/ForwardQModelVertexEquiv.lean`.

- **Prefix-order reflection for canonical semi-complete source addresses (six endpoints, CI pending):**
  the actual directional support walk not only preserves ambient
  prefixes but reflects them, using an admissible path tail and
  uniqueness of root addresses. Strict-prefix relations follow.
  The genuine first-l homogeneous interior address map therefore
  preserves and reflects the model's OWN interior/interior prefix
  order, not merely relations between different Q outputs.
  Model-boundary-to-Q prefix/direction compatibility and the
  published selector on arbitrary semi-complete starred U remain
  separate tasks. See `DualTree/ForwardSourceAddressPrefixIso.lean`.

- **Full homogeneous model/Q prefix isomorphism (eight endpoints, CI pending):**
  the genuine first-l model interior and external boundary, with their
  OWN ambient prefix relation, are canonically prefix-isomorphic
  to every corrected Q support. The proof handles all four combinations:
  two interiors, interior/leaf, leaf/interior, and two leaves,
  using the verified source directional-walk prefix reflection,
  leaf-to-R incidence and fixed Q prefix invariance.
  First outgoing-direction preservation is still separate,
  and equality with the published I_U for arbitrary starred U
  is not claimed. See `DualTree/ForwardQModelPrefixIso.lean`.

- **First-direction reflection for genuine admissible source addresses (four endpoints, CI pending):**
  the directional support walk preserves and reflects every outgoing
  child cone, not merely the prefix relation. The proof explicitly
  recovers an admissible suffix and uses uniqueness of the first
  ambient support direction, so stretched edges cannot silently
  permute model directions. This is the reusable last input for
  checking the first-l model-to-Q canonical map's direction labels.
  See `DualTree/ForwardSourceAddressChildCone.lean`.

- **Direction-labelled first-l model/Q geometric transport (two endpoints, CI pending):**
  every genuine corrected Q support is not only canonically
  prefix-isomorphic to the first-l model interior plus boundary,
  but the realization preserves and reflects the first outgoing
  child direction at every interior node and for every model target.
  Original source-leaf incidence handles external Q marked leaves.
  This does not yet equate the source-relative selector with the
  published Definition 24 I_U on arbitrary semi-complete refinements
  or discharge the mixed Ramsey word/span obligations.
  See `DualTree/ForwardQModelDirectionalIso.lean`.

- **Original simplicity needs only Q-local canonical-selector agreement (three endpoints, CI pending):**
  for any proposed Definition 24 canonical selector I_U and any
  B2 subset of the genuine model boundary, retain the FULL
  original simplicity hypothesis over all starred refinements U,V.
  Its corrected Q pullback is smooth, and admits a TOTAL
  smooth extension, provided I_{Q(w)} agrees with the verified
  source-relative selector only on ACTUAL Q images. This
  discharges the B2/Gamma2 coordinate matching without asking
  for an unnecessarily strong equality of selectors on arbitrary
  U outside the Q image. The Q-local selector identity, printed
  W_* transport, Hall/span and Ramsey iteration remain open.
  See `DualTree/ForwardQPaperSelectorReduction.lean`.

- **Rigidity of the partial Definition 24 canonical walk (six endpoints, CI pending):**
  explicitly separate A_0={[]} from the positive-l external-child
  boundary. Prove that every nonroot first-l interior or
  boundary address has an interior parent, and that two maps
  with the same root and unique-successor step law at these
  parents agree throughout the entire first-l model. The
  genuine support walk is thus the UNIQUE possible local
  canonical map once those two easily testable premises
  are established. This is the next Q-local paper-selector
  proof target; it is not yet discharged.
  See `DualTree/ForwardCanonicalPartialWalkUniqueness.lean`.


- **Complete Definition 24 boundary rigidity (CI pending):**
  the positive-l interior/external-boundary uniqueness argument also
  covers the exceptional A0 singleton root case; a direct support-walk
  corollary is proved. Two further source-facing endpoints bring the
  branch to 1,339 audited declarations. The published selector's Q-local
  root/step laws, word span/Hall and Ramsey steps remain open.

- **Independent proof coverage safeguards:** the source audit rejects
  repeated or foreign transitive-axiom target names, and disallows Lean
  imports following documentation or commands. Endpoint counts are
  not theorem-completion percentages.

- **Actual Q local successor (draft for CI):** identify every immediate
  first-l homogeneous model child as an interior-or-boundary model point,
  then prove its realization is the finite-support immediate successor
  in the corresponding outgoing direction of the corrected Q tree.
  This would establish the actual support-walk local recursion without
  confusing ambient adjacency with support adjacency. The new module
  has seven registered endpoints (target 1,346), subject to the Lean
  build and transitive axiom audit. The original arbitrary-U selector
  and reverse-order starred domain remain independent.

- **Canonical corrected Q support walk (CI pending):** from the
  no-intermediate-vertex finite-support successor theorem, identify the
  actual model/Q vertex map on every first-l interior and boundary
  word with its unique root-directed support walk. In particular the
  A_l boundary walk equals the true D2 projection on each finished
  starred Q image. This eliminates Q-local agreement for the explicitly
  SOURCE-ROOTED walk, but does not yet establish that the published
  arbitrary-U selector uses exactly this root/walk. Nine source-facing
  endpoints are registered (target 1,355); Lean CI pending.

- **Intrinsic rooted semi-complete selector (stacked proof, CI pending):**
  every positive-interior starred U has a unique support root; the
  corrected finished Q output has the SAME root as its original source.
  Its intrinsic-root walk therefore equals the actual D2 projected
  model-A point, not just a walk rooted at an externally frozen source.
  Full arbitrary-U simplicity for this explicit intrinsic selector
  implies Q-smoothness and a total extension. The paper's printed
  selector alignment and reverse-order starred-domain transport remain
  open; thirteen proposed new audit endpoints bring the branch to 1,368.

- **Operational canonical-map bridge for printed I_U (CI pending):**
  a proposed arbitrary-starred canonical map need satisfy its root and
  unique outgoing-direction recursion only on actual Q images. The
  finite-model rigidity proof then FORCES its A_l selector equality,
  yielding paper-style full-ambient simple-colouring smoothness and
  total product extension. The root/step laws are explicit assumptions
  to check against the published semi-complete I_U convention; they
  have not been silently postulated as properties of undefined text.
  Three new source-facing endpoints target 1,371 audited declarations.

- **Uniform semi-complete canonical root including l=0 (CI pending):**
  an arbitrary starred semi-complete U has a unique common prefix
  root whether its support is singleton or nonsingleton. The uniform
  rooted directional walk agrees with the existing positive-l proof,
  and Definition 24's exceptional A0={empty address} maps exactly
  to this intrinsic support root. Root/step rigidity now has one
  statement covering all l. Nine new endpoints target 1,380;
  the reverse-order paper model and Hall/Ramsey induction remain open.

### Lemma 27 final-refinement architecture (16 October; CI pending)

The original printed proof first applies Q to ordinary mixed-product ELEMENTS;
only AFTER the mixed Ramsey step does it construct an ambient variable word f'
whose new variable roots are the projected roots P_i(z) of the selected local
component words f_i. All these new roots belong to the larger COMPLETE ambient
support T, not to the l old source-interior variables in Q(w). Consequently
injecting every independently tagged local variable into the old l roots via a
Hall matching is generally too strong and is **not necessary for the initial
constant-input Q construction** (see the existing verified
`ForwardQAmbientFibreSpan`). The existing conditional Hall theorems remain
valid and useful as separate combinatorial infrastructure, but must NOT be
treated as a hidden Lemma 27 hypothesis.

The new `ForwardQFinalRefinementRoots` module proves, subject to pending CI,
that projections of tagged local addresses are globally injective across
ALL D0/D2 frontier cones, that local prefixes are preserved, and that projected
local variable roots form a finite subset of T disjoint from all original
source roots. This is the first stage of reconstructing the paper's actual
T' and f', rather than artificially matching all local variables to the
fixed old source roots. Eleven source-facing endpoints, target **1,391**.

See `notes/lemma27_final_refinement_architecture_20261016.md`. The next
mathematical steps are COMPLETE-SKEW T' gluing, root-legal construction of f'
on original f-fibres, explicit syntactic f' <= f, and the required inclusion
`[S,f'] subset Q(span(f_i))`, followed by starred-domain correction and
Ramsey iteration. These remain OPEN.

### Candidate final T' support (16 October; CI pending)

`ForwardQFinalSupportCut` now defines the literal finite support
candidate as the complete ambient T vertices at/before the **inclusive
forward cut**, together with the projected local variable roots of the
post-Ramsey mixed word. Fourteen source-facing endpoints (target **1,405**)
check that both parts are subsets of the true T, that the original cut
and old source roots are retained, that projected nodes stay beyond
the cut, and that the two parts are disjoint; projections from
different frontiers are mutually prefix-incomparable. The retained
part is T-relative prefix closed. This is a geometric prerequisite,
NOT a claim of complete skewness, of a legal final variable word, or
of Lemma 27. The unproved next step is the global complete-skew
and uniform f'-fibre construction.

### Reflected prefix and ordered cross-frontier projections (16 October; CI pending)

The proposed `ForwardQFinalProjectionOrder` derives the full
prefix **equivalence** for two projected local addresses from the same
frontier, using the checked inverse canonical address in the complete
T. It also records the exact intrinsic T-rank formula for P_i(z)
and proves that for i<j and |z|<=|w|, the projections
P_i(z),P_j(w) are correctly forward-ordered and have
nondecreasing ambient lengths. These do NOT assume that support
edges are ambient immediate children. Four audited endpoints
(target 1,409) remain CI-pending. The mixed coordinate words'
vector-complete clauses must still provide the necessary
tail-length comparisons and the assembled T' still needs
its own complete-skew argument.

### Mixed vector completeness supplies projected-root order (16 October; CI pending)

`ForwardQFinalVectorOrdering` now extracts the two actual
cross-coordinate length inequalities from the `vectorCompleteB`
field of the post-Ramsey `LocalMixedWord`: at equal intrinsic local
levels r<q, roots in coordinate i<j have lengths |z|<=|w|;
at successive levels r and r+1 (r<q-1), every pair of coordinates
has |z|<|w|. These are the exact hypotheses for the preceding
projected-root ordering theorem. Thus same-level and successive-
level variables in increasing frontier order project to
forward-ordered ambient T roots, with nondecreasing ambient lengths.
The combined branch targets 1,415 audited endpoints, CI pending.

This is still NOT proof that candidate T' is complete/skew: the
relative intrinsic ranks in T', cross-comparisons at reversed
coordinate indices for successive levels, branching and the
retained/new interface must be checked independently.

### Exact target-height budget for printed T' (16 October; CI pending)

An adversarial revisit of Lemma 27, page 29, revealed the printed
candidate was M-rank **TRUNCATED**, not the entire set of projected
local variable roots. The actual condition is
`height_ws(f_i)(z) + height_T(frontier_i) < M`, where **M is the
FINAL target height**, and the Frame parameter `m` denotes the
EARLIER rank of the source cut t0. Conflating those two heights
would make the gluing proof prove the wrong theorem.

`ForwardQFinalHeightBudget` introduces an explicit M and filters
the genuine tagged local roots by precisely that condition.
The resulting `finalBudgetSupport` consists of the same retained
initial T prefix plus only the selected projected roots.
It is a finite subset of the original unfiltered
`candidateSupport`, hence of T; retained and projected parts
stay disjoint, the original cut/source roots remain present,
every selected projection carries a rank-budget witness, and the
construction is monotone in M (15 endpoints, target 1,430;
CI pending). This fixes the SET, not its full complete-skew
structure. Intrinsic ranks in the assembled support, its
complete branching and the actual f' word remain open.

### First intrinsic-rank predecessor reductions (16 October; CI pending)

`ForwardQFinalBudgetPredecessors` begins the actual `heightAt`
calculation for the EXACT M-filtered final support. It proves that a
retained old ambient-support vertex prefixes a new projected
P_i(z) iff it prefixes the frontier t_i, so the old predecessor
contribution depends only on the frontier, not the local address.
Every strict T predecessor of t_i is retained. The selected-local-root
budget is hereditary under strict prefixes inside each component
support; those local prefixes stay strict after projection.
Five checked endpoints are proposed (target 1,435), pending Lean CI.

This is a necessary geometric predecessor decomposition, NOT yet a
formula equating final-support intrinsic height with
h_T(t_i)+h_ws(f_i)(z). The predecessor-set cardinality/counting
lemma, all complete-skew axioms and the global final f' variable
word remain separate outstanding obligations.

### Rank preservation for retained T' vertices (16 October; CI pending)

The `ForwardQFinalRetainedRanks` module now treats the OLD
predecessor contribution quantitatively. The strict T-predecessor
set of each corrected frontier is exactly its retained-predecessor
set, so its cardinality is precisely the frontier's ambient
support rank `height_T(frontier_i)`.
For every retained initial-cut T vertex t, its intrinsic
height in the FULL rank-budgeted final support `T'_M` equals
its original intrinsic height in T: adding projected roots
does not insert ancestors of t or remove any previous ones.
These claims rely on generic finite-support predecessor-cardinality
lemmas. Nine new axiom endpoints (target 1,444) await CI validation.

This proves the old part of the desired projected rank formula,
NOT the local new-root predecessor count nor M-complete skewness.
The latter still requires a disjoint predecessor decomposition,
the cardinality of projected local strict predecessors, the
branching axioms, and the final variable word f'.

### Exact classification of selected new projected predecessors (16 October; CI pending)

The proposed `ForwardQFinalSelectedPredecessors` proves
that a selected projected vertex can lie strictly below
P_i(z) only if it comes from the SAME sorted outside-cut
frontier i. Its projected strict prefix relation reflects
to a strict local support prefix w of z. If z itself
passes the target-height M filter, then the hereditary
budget theorem shows that w is selected automatically.
Thus selected new strict predecessors of P_i(z) are
**exactly the projections of proper local variable-support
predecessors of z**, without an independent Hall matching.
Four new source-facing endpoints target 1,448 (CI pending).

The final arithmetic step is to count this set via
injectivity of the canonical projection, combine it
with the already checked retained count h_T(frontier_i),
and conclude the intrinsic rank identity. No complete
skewness or final f' has been claimed.

### Projected local predecessor count (16 October; CI pending)

`ForwardQFinalProjectedPredecessorCount` carries out the
finite cardinality argument for NEW support roots. Given a
local variable-support root z that satisfies the exact target-M
rank cutoff, the strict new predecessors of P_i(z) are
exactly the image of the actual strict support predecessors w
of z under the injective P_i. Passing to Finset cardinalities
identifies their number with
`height_(ws(f_i))(z)`. Six proposed source-facing endpoints
(target 1,454) await CI.

Together with the already checked old retained-predecessor
count `height_T(frontier_i)`, this supplies BOTH summands
of the desired full final-support intrinsic rank identity.
The last step is to split the filtered predecessor set into
these two DISJOINT families and add their cardinalities.
Neither the complete-skew axioms nor final ambient f'
word/refinement has yet been proved.

### Full intrinsic projected-root height formula (16 October; CI pending)

The proposed `ForwardQFinalIntrinsicRank` combines the exact
old retained predecessor count with the exact local projected
predecessor count. Since the retained and selected projected
root families are disjoint, their filtered predecessor sets
form a disjoint union. Consequently every selected P_i(z) in
the EXACT target-M final support satisfies

  height_(T'_M)(P_i(z)) =
    height_T(frontier_i) + height_(ws(f_i))(z).

By the *definition* of the printed target-height budget,
every selected new projected root has height_(T'_M)<M.
This is the first full projected-support INTRINSIC rank
calculation; six selected Lean endpoints target 1,460
(CI pending). The separate verified retained-rank formula
supplies the corresponding answer for all old vertices.

The remaining obligations before claiming M-complete skewness
are the exact branching and uniqueness of directional support
successors, the skew rank/ambient-length ordering, and
the correct parameter bounds ensuring all retained vertices
also have rank<M. Then the final f' word, syntactic
refinement, Q(span) containment, starred domain and
Ramsey induction still need proofs.

### Uniform target-rank bound for the exact final support (16 October; CI pending)

The proposed `ForwardQFinalRankBound` completes the target-M
RANK BOUND under the explicit necessary numerical hypothesis
`m < M` (where m is the earlier source-cut rank). Every
retained vertex has ambient T-rank at most m by the existing
forward-order rank lemma and has the same intrinsic rank in
the assembled T'_M support; hence its final rank is <M.
Every selected projected root already has rank <M by
the exact local + frontier rank formula and strict
budget filter. Therefore EVERY vertex of T'_M has
intrinsic support rank below target M. Four proposed
source-facing endpoints (target 1,464, CI pending).

This uniform height bound alone is NOT an M-COMPLETE
skew-tree theorem. Full b-branching at every nonleaf,
the skew ambient length/forward auxiliary ordering, and
the actual ambient final variable-word construction
remain independent proof obligations.

### Two-frontier height-budget dichotomy (16 October; CI pending)

The **actual** mixed Ramsey variable word has local dimension q=M-m
for the final target height M and original cut rank m. Every
minimal outside-cut frontier has ambient T-height **m OR m+1**.
The proposed `ForwardQFinalTwoFrontierBudget` now derives from the
mixed word's `vectorCompleteB` hypothesis that every genuine
local component support root has height <q. It follows that:

* At a rank-m frontier the final M=m+q filter selects
  **all** genuine local support variable roots.
* At a rank-(m+1) frontier it selects exactly roots with
  local intrinsic height + 1 < q.
* At a rank-(m+1) frontier and q≤1, no new root is selected.

The one-level discrepancy is essential for the full branching
argument. Seven additional audit endpoints target 1,471 (CI pending).
No global complete-skewness, f' construction, or theorem is claimed.

### Existence of genuine selected local roots above frontiers (16 October; CI pending)

The proposed `ForwardQFinalLocalRoots` proves root existence in
every **actual local q-complete variable support**, including its
singleton case, and constructs an intrinsic-rank-zero bounded root
that is a prefix of all other local support nodes. The exact
M=m+q cutoff then guarantees that its actual ambient projection
belongs to the selected final support at rank-m frontiers and at
rank-(m+1) frontiers when q≥2. Upper frontiers contribute no
new roots when q=1, exactly as required for the last-level base
case. Eight selected endpoints target 1,479 (CI pending).

This guarantees nonempty projected cone supports where needed;
it does not yet show every retained nonleaf has a successor in
EACH ambient direction or that the joined support is complete
skew. The next arguments must use the original T's full
branching and the local supports' q-completeness.

### Full local branching and selected directional successors (16 October; CI pending)

For a genuine post-Ramsey mixed-word component (f_i), every
local support root of intrinsic rank (r) with (r+1<q)
has a unique immediate **support** successor in every one of
the (b) ambient directions. That successor is a genuine
bounded variable support root of rank (r+1); it need not
be an immediate ambient child.

The proposed `ForwardQFinalLocalBranching` proves that these
successors remain in the exact selected final support
at a rank-(m) frontier automatically. At a rank-((m+1))
frontier they remain selected when (r+2<q), precisely
accounting for the upper frontier's shorter local budget.
Six selected axiom endpoints target **1,485** (CI pending).

The outstanding gluing step must establish that these
projected successors are the actual immediate successors
inside the UNION with the retained initial support; no
complete-skewness or global f' claim is inferred yet.

### Selected local immediate support edges in the glued T'_M (CI pending)

`ForwardQFinalImmediateGluing.selected_local_immediate_is_final_immediate`
proves that if selected local roots z,w form an immediate support edge
in component i, their actual projections P_i(z),P_i(w) form an immediate
edge of the **whole** target-filtered final support T'_M. No retained
vertex can intervene beyond the cut. Every intervening projected root
would come from the same frontier and contradict the local immediate
edge by prefix reflection. This does not identify ambient adjacency,
nor prove direction labels or the retained/new boundary.
One selected axiom endpoint targets 1,486 (CI pending).

### Exact first outgoing direction under canonical frontier projection (CI pending)

`ForwardQFinalProjectionDirection` proves that the actual
forward-complete canonical support embedding preserves the first
outgoing direction at every bounded source address. Specializing
to the genuine corrected frontier maps P_i via
`inverse_T(P_i(z))=inverse_T(frontier_i)++z` gives:
if `z++[dir]` prefixes `w`, then `P_i(z)++[dir]`
prefixes `P_i(w)`. This proof does not mistake abstract
prefix-order preservation for directional preservation; it
uses the actual support successor walk, and admits stretched
ambient edges.

Combined with the separately merged immediate-edge gluing
theorem, this is a key step toward full branching of T'_M.
Two selected proof endpoints target 1,488 (CI pending).
The retained/new branching interface and complete skew
order clauses remain open.

### Actual direction-labelled immediate successors for selected new roots (CI pending)

`ForwardQFinalProjectedFullDirections` combines local
q-complete branching, the proof that consecutive intrinsic
ranks determine an immediate local edge, the verified
immediate-edge gluing into the WHOLE final T'_M support,
and direction preservation under the canonical P_i map.

At a rank-m frontier, every local root of rank r with r+1<q
has a genuine immediate T'_M successor in each specified
ambient direction. At a rank-(m+1) frontier the correct
condition is r+2<q. The support edges may be stretched.
Four selected source-facing endpoints target 1,492
(CI pending).

This establishes directional existence only for
appropriately early NEW vertices. Uniqueness of all
full-support directional successors and the retained/new
boundary remain to be proved before M-complete skewness.

### Retained T-support edges and frontier crossings (CI pending)

The proposed `ForwardQFinalRetainedEdges` divides the
immediate edges s→t of the original complete ambient
support T with retained parent s at/before the inclusive
cut into two cases.

If t is also retained, that edge is immediate in the
WHOLE rank-budgeted T'_M support; no projected vertex
can intervene as a predecessor of an old retained node.

If t lies after the cut, it is itself a minimal
outside-cut frontier of T. Its intrinsic T-rank is
necessarily m or m+1, by the checked forward frontier
rank band. Three selected source-facing endpoints target
1,495 (CI pending).

The remaining retained/new branching argument must
identify the corresponding sorted frontier coordinate,
select its true local support root P_i(z_i), and prove
that its projected node replaces t as the immediate
direction-labelled T'_M successor. This does not yet
establish complete skewness or the final word f'.

### Retained-to-projected root edges via the intrinsic rank gap (CI pending)

The proposed `ForwardQFinalRetainedFrontierGluing` uses the
exact rank calculation to simplify the old/new case.
If an immediate ambient T-edge goes from retained s
to a genuine frontier t_i, and the true local component
root z_i is selected, then its projection P_i(z_i)
has final intrinsic rank exactly height_T(t_i),
since the local root has rank zero. That equals
height_(T'_M)(s)+1 by immediate T-rank increase and
retained-rank preservation.

Together with s prefix t_i prefix P_i(z_i), the verified
rank-gap-implies-immediate lemma makes s→P_i(z_i)
a genuine immediate edge of the FULL final support.
The edge stays in the same first ambient direction
as the original T-edge. Three selected axiom endpoints
target 1,498 (CI pending).

Completing retained branching now requires locating
each crossing T-edge in the actual sorted frontier
enumeration and checking selection of its local root
under the two rank cases. The complete-skew length
order and final variable word f' remain open.

### Crossing retained T-edges now yield selected projected successors (CI pending)

`ForwardQFinalRetainedCrossing` eliminates the artificial
preselected-frontier-index hypothesis. Every immediate
ambient T-edge s→t crossing from a retained s beyond the
inclusive cut has t itself as a genuine member of the
forward-SORTED frontier list. If s has room for another
level in the final target M=m+q, the authentic local
coordinate root z_i is selected above that frontier.

At rank-m frontiers all local roots are selected. At
rank-(m+1) frontiers, the immediate ambient T-rank
increase and the available final height force q≥2,
so the local height-zero root passes the shorter cutoff.

The previously checked one-rank-gap gluing theorem now
makes s→P_i(z_i) an actual immediate edge in the FULL
T'_M in the same first ambient direction, without
choosing the frontier index as a hypothesis.
Three proposed source-facing endpoints target 1,501
(CI pending).

The next proof can case-split the original T directional
successor of ANY early retained vertex into retained or
outside-cut branches. Uniqueness of every full-support
directional successor and the global skew-order clauses
remain open, as does the final f' word.

### Retained-root directional existence in the final support (CI pending)

For the corrected Lemma 27 construction with final target
`M=m+q`, the proposed module `ForwardQFinalRetainedFullDirections`
proves that every retained root s of intrinsic final-support rank
r with r+1<M has an **immediate successor in every ambient
direction in the entire glued T'_M**, under the explicitly
stated ambient-height capacity bound `m+q≤k`.

The proof uses the complete original ambient support T to
select its unique immediate successor in the requested
direction. If that successor stays before the cut, the
checked retained-edge gluing applies. If it crosses the
cut, the previously verified actual sorted-frontier
replacement theorem supplies a selected projected local
root in the SAME direction. This establishes nonempty
immediate directional witness families, not their uniqueness.
The capacity bound needs to be reconciled with the actual
mixed-word parameter choices in the paper before any
unconditional M-complete skew claim.

Two source-facing endpoints target 1,503 (CI pending).
The remaining structural obligations are directional
UNIQUENESS, new projected vertices at all eligible
levels, global skew ordering and complete-height
boundary conditions, then the final ambient f'.

### Mixed component completeness forces the needed ambient height budget (CI pending)

The proposed `ForwardQFinalMixedCapacity` derives an important
numerical parameter bound instead of postulating it. For every
genuine coordinate i of a q-complete mixed-variable word f
whose roots are BOUNDED at local height h=k-(m+1), we have
`q≤h`, and therefore `m+q≤k`. A terminal local
support root has intrinsic height q-1, and a duplicate-free
support cannot have more proper support prefixes of a word
than its actual word length. Its bounded local word length
is <h, forcing the claimed inequality.

The coordinate-index premise is significant: if the mixed
product has no coordinates, `vectorCompleteB` is vacuous
and cannot imply a bound on q. In the final branching
application a real frontier index or an occupied outgoing
direction must provide the needed coordinate. Three
source-facing endpoints target 1,506 (CI pending).

This closes the numerical capacity used by the preceding
retained-direction existence proof whenever a genuine
coordinate is available. Full M-complete skewness still
requires uniqueness and the global ordering clauses.

### Unconditional retained-root branching existence in all directions (CI pending)

The proposed `ForwardQFinalRetainedUnconditional` eliminates
the numerical capacity and preselected frontier-index assumptions
from retained-root directional EXISTENCE. Each requested direction
`dir:Fin b` yields an actual immediate ambient T successor of
the original cut (using c.hearly). Its T-rank increases by one,
so it necessarily lies beyond the corrected inclusive cut.
The previously verified crossing-to-sorted-frontier lemma gives
a genuine mixed coordinate i. The q-complete bounded word at
i then forces m+q≤k; this supplies precisely the capacity
needed for the retained-direction construction.

Consequently every retained support vertex whose ACTUAL final
intrinsic rank r satisfies r+1<m+q has an immediate successor
in the correct ambient direction in the WHOLE assembled T'_M.
The branchWitnesses family is therefore nonempty. No extra
capacity or coordinate hypothesis is added, and b=0
is handled vacuously via the direction parameter.
Four source-facing endpoints target 1,510 (CI pending).

Still open: uniqueness of directional immediate successors,
the complete-skew rank/length ordering, complete terminal
height, and final f'/Q-span/Ramsey construction.

### Full directional EXISTENCE throughout the exact final support (CI pending)

The proposed `ForwardQFinalAllDirectionExistence` now
combines the retained-vertex theorem with the selected
projected-root theorem. For an M-budget-selected local
root P_i(z), the exact intrinsic-final-rank formula
and the two possible frontier ranks (m or m+1) convert
the condition `height_(T'_M)(P_i(z))+1<M=m+q`
to exactly the local-support inequalities already
required by the checked projected full-direction lemmas.
For a retained root the previously checked actual
cut/frontier and local-dimension capacity arguments
apply without added assumptions.

Hence for EVERY vertex s of the true filtered T'_(m+q),
if its ACTUAL final intrinsic rank r satisfies r+1<M,
and for EVERY dir : Fin b, there exists a genuine
IMMEDIATE T'_M support successor t in that exact
ambient direction. Every branchWitnesses list is
therefore nonempty. These statements do not assert
uniqueness, and do not silently identify ambient
edges with one-letter edges.

Three new curated endpoints target 1,513 (CI pending).
The remaining structural theorem must prove there is
AT MOST ONE witness in each direction, then verify the
global skew order/length axioms and last-level leaf
condition. The ambient f' word, Q-span containment,
reverse auxiliary-order text and Ramsey recursion
remain separate work.

### Converse classification of immediate children of retained vertices (CI pending)

The forward Lemma 27 construction already gives immediate
children in every required direction. To prove uniqueness,
we must show that EVERY possible immediate final-support
child arises from those constructions.

The proposed `ForwardQFinalRetainedChildConverse`
proves three inverse facts. First, any immediate T'_M
edge whose endpoints are both retained was already
immediate in the original ambient complete support T:
an intermediate T vertex would survive the initial cut.
Second, if an immediate final child of retained s
is a selected projection P_i(z), the exact rank
equations force frontier_i to be an immediate T child
of s and the LOCAL intrinsic height of z to be zero.
Third, a q-complete local support has a unique
rank-zero root, so z is precisely the previously
constructed `localRoot c f i`.

This reduces uniqueness at a retained vertex to the
known unique directional successor in T. Three new
source-facing endpoints target 1,516 (CI pending).
Uniqueness for projected parents and global skew
order/length clauses remain open.

### Converse classification of selected projected immediate children (CI pending)

The proposed `ForwardQFinalProjectedChildConverse`
shows that any immediate child of a selected projected
parent P_i(z) in the FULL filtered final support must
itself be a selected P_i(w) from the SAME frontier
coordinate i. Retained nodes are excluded by the
inclusive cut, and other frontiers have incomparable
cones. The local z is a strict prefix of w.

The full-support immediate rank gap is exactly one.
Using the checked intrinsic final rank formula at
both projected endpoints cancels their common
ambient T frontier rank and forces the local
height gap to be exactly one. Thus z→w must
already be an immediate LOCAL support edge.
No abstract prefix-order isomorphism or Hall
matching is assumed.

Two source-facing endpoints target 1,518 (CI pending).
This is the key converse interface needed to
transfer unique directional branching from the
q-complete local component supports to all
selected projected vertices. Retained direction
uniqueness, meet closure, skew ordering and final
f'/Q-span containment remain separate.

### Corrected frontier projections reflect labelled first directions (CI pending)

The proposed
`ForwardQFinalProjectionDirectionReflect.projected_childCone_iff`
establishes the exact two-way implication
`z++[dir] ⊑ w ↔ P_i(z)++[dir] ⊑ P_i(w)`.
Prefix reflection gives a nonempty local suffix;
the already verified directional-preservation theorem
places its first letter into the matching projected
ambient cone. Equal-length prefix uniqueness then
forces that local first letter to be exactly dir.
No ambient one-letter edge hypothesis is used:
projected support edges may be stretched.

This is the precise direction-labelled equivalence
needed to transfer local q-complete uniqueness to
selected projected final-support children. One
additional source-facing endpoint targets 1,519
(CI pending). Retained unique branching and
global forward skew/complete order conditions
remain open.

### Same-direction uniqueness at selected projected final-support vertices (CI pending)

The proposed
`ForwardQFinalProjectedDirectionUniqueness.selected_projected_atMostOneDirection`
proves that two immediate final T'_M children of any
selected P_i(z) in the same ambient outgoing direction
must be EQUAL. Every final immediate child is a genuine
local immediate support child in the SAME frontier
(by the checked converse), and the corrected P_i map
reflects its labelled first direction. The actual
q-complete local support is ambient meet-closed
whenever it contains a genuine immediate edge,
hence has at most one immediate child per direction.

This proves directional UNIQUENESS for all projected
parents without assuming T'_M itself is complete skew
or meet-closed. One source-facing endpoint targets
1,520 (CI pending). Together with the previously
checked full-direction existence theorem, it would
settle the branching count at selected NEW vertices.
Retained same-direction uniqueness, global forward
skew ordering, complete boundary ranks, final f'
and Q-span/Ramsey remain open.

### Retained-parent immediate-child directional uniqueness (17 October; CI pending)

`ForwardQFinalRetainedDirectionUniqueness` proves that every final
immediate child of a retained parent corresponds to a unique
genuine immediate ambient T child in the SAME first direction.
The final child either survived the corrected cut unchanged
or is the projected canonical local root at an outside-cut
frontier. Since original complete T is meet-closed, the
ambient immediate child is unique in each direction. A
retained vertex cannot equal an outside-cut frontier, and
two projected children with the same frontier share the
same canonical local-root image. Therefore retained final
parents have AT MOST ONE child per direction without
assuming T'_M is already complete skew.

Two new selected endpoints target 1,522 (CI pending).
Together with verified projected-parent uniqueness, this
will finish the per-direction uniqueness assertion for
all final support vertices, once CI succeeds.

### Exact branching below the final level of T'_M (17 October; CI pending)

The proposed `ForwardQFinalExactBranching` first proves a
general reusable finite-support lemma: for duplicate-free S,
at-most-one immediate successor per direction together with a
nonempty direction witness gives `uniqueBranchB`.
Its full final-support `AtMostOneDirection` theorem combines
independent checked projected-parent uniqueness with the
retained-parent uniqueness bridge (currently in PR #346).

Using the previously proved existence of an immediate
T'_M successor in every direction whenever
`height_(T'_M)(s)+1 < m+q`, it proves that each such
vertex has EXACTLY ONE successor per direction, hence
exactly b immediate SUPPORT successors overall. This
is the complete branching-count clause below the last
intrinsic level, including stretched ambient support
edges and both cut-rank classes.

Four further curated endpoints target **1,526** (CI pending).
The last-level leaf condition, global skew rank/ambient-length
ordering, and the actual word f' with Q-span containment
remain OPEN. The final theorem is not yet formalized.

### Exact final leaf-or-b-branching clause (17 October; CI pending)

The proposed `ForwardQFinalLeafBranchClause` checks the
remaining LAST-LEVEL case for the exact rank-filtered
support T'_M. Every selected vertex has actual intrinsic
rank <M; if one at rank M-1 possessed an immediate
successor, the generic support-rank increment theorem
would produce a vertex of rank M, contradiction. Thus
last-level vertices are leaves.

For positive b and q, all earlier vertices have exactly
b>0 immediate support successors by the separately
verified existence/uniqueness chain, while final-level
vertices have none. This proves the ENTIRE executable
Boolean complete-branching clause of T'_(m+q).

The clean reduction states:
`completeB forwardAuxB (m+q) T'_M = true`
if and only if
`skewB forwardAuxB T'_M = true`.
The skew condition itself is NOT proved by this
equivalence. Three selected endpoints target **1,529**
(CI pending); global skew length/auxiliary ordering,
final word f', Q-span containment and Ramsey induction
remain open.

### Actual final-support rootedness and meet closure (17 October; CI pending)

The ambient forward-complete support T has a canonical
root r that lies at/before the corrected inclusive cut.
The exact final target-filtered support T'_M is a subset
of T and retains that initial segment. Hence r belongs
to T'_M and prefixes every final-support vertex; its
Boolean rootedB predicate is true for every target height.

For M=m+q, the independently verified all-parent
AtMostOneDirection theorem and the generic
rooted+unique-directions result establish ambient
MEET CLOSURE of the actual final T'_M support.
This does not assume final skewness, and is independent
of the already verified Boolean complete branch/leaf
clause. Together these reduce M-completeness to the
remaining global forward skew auxiliary length/order
and special witness conditions.

Four new curated endpoints target 1,533 (CI pending).
Full skewB and the final ambient word f' with
Q-span containment remain OPEN.

### Retained/retained global forward-skew length clauses (CI pending)

The checked intrinsic rank preservation for retained vertices,
together with the source's genuinely forward-complete skew
axioms, gives clauses (ii) and (iii) of the final-support
skew definition for **pairs of retained vertices**:
equal intrinsic ranks ordered by forward lex have
nondecreasing ambient lengths; strictly increasing
ranks imply strictly increasing lengths. The latter
also yields corrected forward auxiliary monotonicity.
Five new registered endpoints bring the proposed curated
axiom audit to 1,538. Full CI pending.

This is NOT global skewB: retained/projected and
projected/projected pairs, plus skew witness clause (iv),
remain open, as do f' and the Ramsey inclusion.

### Exact rank-m frontier lex position relative to retained vertices (CI pending)

A length-first forward-sorted frontier is NOT automatically
forward-lex ordered. The proposed
`ForwardQFinalFrontierLex` proves the relevant special
case instead: a retained T vertex of intrinsic rank m
lies lex before the cut, while every outside-cut frontier
of T-rank m lies lex after the cut. Distinct equal-rank
support vertices are prefix-incomparable, so every
descendant P_i(z) of such a rank-m frontier also lies
lex AFTER the retained rank-m vertices, even for
stretched support edges.

Six source-facing endpoints (including custom finite
lex transitivity) target 1,544, CI pending. This should
eliminate the would-be reversed lex orientation in the
retained/projected equal-final-rank skew clause II.
The mixed rank-m/rank-(m+1) projected comparisons
still need their distinct lexical geometry.

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
- The actual full-frontier Q word now has a proposed
  **mixed-product evaluated-span bridge**: if a genuine corrected-starred
  input x belongs to the span of a variable mixed-product word f, then
  each coordinatewise Q symbol at P_i(z) is exactly the constant
  carrying the evaluation of f_i under a local substitution σ_i.
  All component assignments can be selected simultaneously, and
  outside all frontier cones the old source word is unchanged.
  These are independent LOCAL assignments, not a single substitution
  into the limited old Q-source roots, so no global span-preservation
  or Ramsey step follows (5 source-facing Lean endpoints, CI-green on PR #248).
- The canonical smoothness fingerprint now has a proposed
  **literal corrected R/B₂ marker interface**. A subset B₂ of
  actual source signature markers determines exactly Gamma₂ via the
  checked R ↔ D₂ coordinate bijection; B₁ markers preserve whole
  words but hide marked points, whereas B₂ masks inside-cone
  letters and records the point and outside-cone letters.
  Equality of these records is exactly Definition 21 smoothness,
  and arbitrary smooth corrected-starred colourings factor through
  this concrete marker record. The remaining paper-specific
  obligation is the canonical address transport from its abstract
  Definition 24 A=B₁⊔B₂ to the actual R, followed by verifying its
  particular colouring factors through the record (7 source-facing Lean endpoints, CI-green in PR #250).
- A verified **strict evaluated-span loss** theorem quantifies
  the genuine-variable transport obstruction: over any alphabet
  with two distinct letters, identifying two different local
  variable names that both actually occur strictly shrinks
  the evaluated span. At a corrected Q frontier with m+2
  such names and at most m+1 visible old roots, any
  root-aligned transport necessarily identifies some names,
  so it cannot preserve the FULL local raw-word span.
  This is a conditional limitation on the naive Lemma 27
  repair, not a counterexample to the main Ramsey theorem
  (3 verified endpoints in merged PR #249).
- The full local two-letter evaluated span has a verified **exact
  injectivity criterion**: a pure variable-name transport preserves
  every evaluated assignment if and only if it is injective on the
  local variable names that actually occur. Unused names may be
  identified freely. The positive direction extends arbitrary
  source assignments to the renamed target variables using a
  partial inverse; the converse uses the strict span-loss witness.
  The criterion is specialized to the actual corrected Q-frontier
  raw local word and old source-variable-root subtype. This is
  the precise remaining LOCAL span condition, not proof that
  the paper supplies an admissible injective assignment or
  completes the GLOBAL mixed Ramsey span (4 checked endpoints in merged PR #251).
- A proposed **sharp single-frontier span-capacity theorem** now
  matches the number q of genuine occurring local variable names
  against the length |V_i| of actual visible old source roots.
  If q≤|V_i|, an explicit first-q visible-root injection is
  geometrically aligned throughout that cone and preserves its
  FULL evaluated raw-word span. Conversely, if all q names
  really occur inside that cone and the enlarged local alphabet
  has two letters, any aligned full-span-preserving root map
  forces q≤|V_i|. This exact iff still does not establish
  compatibility of root assignments ACROSS cones or the printed
  Lemma 27 span, simplicity and Ramsey iteration
  (6 verified Lean endpoints in merged PR #252). At multiple
  frontiers a GLOBAL independent-variable translation requires a
  Hall-type matching condition on the unions of visible old-root
  sets; separate per-frontier capacity inequalities alone do not
  suffice. This is recorded as an unverified author-facing TODO.
- **Global independent-variable allocation has a sharp proposed Hall
  matching criterion.** Tags (i,z) remember their sorted D₀/D₂
  frontier; each tag can use only actual old source variables whose
  roots are visible above frontier i. A globally injective,
  root-aligned assignment exists exactly when every set of tags
  has at least as many distinct available old roots as tags.
  By the checked injective-on-occurrences theorem this matching
  preserves the entire evaluated span of the disjoint union of
  local cone words; conversely, when all declared tagged names
  occur and the enlarged alphabet has two letters, preserving the
  full span forces Hall's inequalities. This is NOT yet the
  paper-specific global Q word, colouring compatibility or
  Ramsey recursion (8 CI-verified endpoints in merged PR #253).
- **Only genuinely occurring local variables consume global
  matching capacity.** The new proposed refinement masks symbols
  outside their own complete-support frontier cones, tags only
  variable names ACTUALLY appearing inside those cones, and applies
  Hall's condition to that finite occurring-name subtype. A matching
  extends to a total root map by assigning an unused old cut variable
  to unused names, and preserves the full independent-coordinate
  evaluated span. Conversely, over a two-letter alphabet,
  full-span preservation and visible occurring roots imply Hall.
  Matched roots are prefix-aligned at every occurrence. The
  *particular* raw words and colour-factorization from Lemma 27
  remain open (8 CI-verified endpoints in merged PR #254).
- Under the exact occurring-variable Hall condition, a proposed
  **single conditional FULL-frontier Q-word constructor** now
  combines the matched old source-variable roots with the
  source-facing visible-ancestor auxiliary decoders R_i.
  Local variables are tagged by their actual frontier indices,
  so independent names from different cones are not silently
  identified. Masked raw symbols preserve the original three
  constructors inside each genuine cone, and Hall visibility
  discharges genuine-variable root alignment. The construction
  yields an actual legal starred Q word on the corrected Q support
  AND preserves the full evaluated independent tagged-coordinate
  span under the same global root allocation. This does not yet
  instantiate the paper's specific raw words, prove its signature
  or simple-colouring factorization, or finish its Ramsey induction
  (5 source-facing endpoints, pending CI).
- A **simultaneous actual-Q variable-evaluation bridge** is proposed:
  under Hall's inequalities for the ACTUALLY occurring tagged cone
  variables, one legal corrected full-frontier Q starred word (chosen
  independently of evaluation) realizes EVERY assignment to all
  independent local variable names by a SINGLE assignment to the
  old source roots. Equality is verified pointwise at each original
  D0/D2 cone-variable occurrence, not only as an abstract span
  identity. An absolute capacity theorem shows that Hall is
  IMPOSSIBLE when the total number of occurring independent
  names exceeds the total number of old source roots. Neither
  paper-specific Hall, auxiliary/outside-cone compatibility,
  simple-colouring factorization nor the Ramsey induction follows
  (4 proposed source-facing endpoints in PR #256; requires CI).

- **One global ambient substitution realizes the entire corrected
  Q word.** The input carries an explicit syntactic refinement
  g'=f[rho]. For each ambient f-variable root, the Q substitution
  uses rho on early/cut fibres and the concrete R_i-decoded
  enlarged letter on later fibres. The whole-domain identity
  g_w=f[rho_w] follows, not just a collection of projected-root
  equations. Consequently the FINISHED legal corrected starred
  Q output satisfies both S_w subset ws(f)=T and
  [g_w]_Lambda subset [f]_Lambda. This needs no Hall matching and
  no two-letter assumption because the substitution is built
  explicitly. It remains conditional on the corrected forward
  order and the syntactic source-refinement premise; Def24
  smoothness and the final f' Ramsey refinement are still open
  (7 proposed source-facing endpoints, CI pending).

- The **corrected full f-fibrewise Q word now has its variable-root
  well-formedness proof**: old variable roots are retained, and any
  emitted variable at an arbitrary ambient position is rooted above
  that position. In a late fibre the key prefix chain is old source
  root < visible frontier ≤ original f-variable root ≤ occurrence,
  so the proof uses f's FIBRES, not geometric cone membership of the
  occurrence. A genuinely legal StarredWord on the exact corrected
  semi-complete Q support is constructed and retains the complete
  projected full-fibre letter/R_i equation. This advances Q from
  a conditional symbol scaffold to a real corrected starred word.
  Hypotheses still include the explicit syntactic g'=f[rho]
  witness and forward-sorted corrected Wstar points. Def24
  simplicity-to-smoothness and the final f' refinement remain
  open (9 proposed source-facing endpoints on the follow-up branch,
  awaiting Lean CI).

- A new **genuinely ambient-fibrewise Q symbol map** reads the
  original ambient f(s) BEFORE consulting any frontier.
  Original constants stay untouched; early/cut variables use g',
  which is proved uniform on f-fibres; post-cut f-variable roots
  choose their unique frontier, recover their correct inverse
  support tail, and decode the actual enlarged-alphabet letter by
  R_i or as an original constant. It proves paper clause (iv)
  on the ENTIRE original f-variable fibre, including ambient
  positions outside the cone of the projected root. It avoids
  conflating root coordinates with ambient positions and requires
  no Hall matching. Further work must prove root alignment of
  emitted old variables and package the word on the Q starred
  support, then establish simplicity-to-smoothness and the
  final variable refinement (11 proposed source-facing endpoints
  in PR #259, pending Lean CI).

- The **ambient f-fibre dependency** is now tracked as an
  explicit strengthening of the corrected Q frame: supply the real
  variable word f with exactly the complete support T, and a
  syntactic substitution proving the starred source word g' refines
  f. This yields uniformity of g' on whole ambient f-variable fibres,
  retains the old source variables and cut, and preserves all old
  alphabet constants. The construction is conditional on a
  substitution witness (evaluated-span inclusion does not supply
  one for singleton alphabets). The five-case paper Q symbol
  definition on all ambient positions, simple colouring pullback
  and final f' remain unverified (10 proposed source-facing
  endpoints in PR #258, pending Lean CI).

- The **original Q construction uses ORDINARY enlarged-alphabet
  local words, not independent local cone variables**. A new
  source-facing module instantiates the verified corrected Q
  full-frontier decoder on actual mixed-product inputs with alphabet
  Lambda + Fin(m+1): original letters remain constants; auxiliary
  labels are sent through the literal visible-ancestor R_i; the local
  variable type is EMPTY. At every genuine canonical projected
  support position P_i(z), the decoded Q symbol and its evaluation
  reproduce exactly this two-case rule, and auxiliary erasure leaves
  D2 points and the Q support unchanged. NO Hall matching is required.
  However the present Frame records (S,g') and its enclosing T but
  not the ambient source word f and its fibres. The paper's full
  formula (i)--(v) classifies ambient positions by f(s), NOT merely
  by their frontier cone; hence the new result does NOT yet verify
  the complete printed g_w. Adding f and proving a fibrewise Q
  decoder is the next obligation (9 proposed source-facing endpoints
  in PR #257, Lean CI required).

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
audits **1108 source-facing declarations** for transitive
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
`ForwardQVariableSpanCollapse` proves the strict two-letter span loss
when genuinely occurring cone-variable names are identified.
`ForwardQSpanExactInjectivity` characterizes full local span preservation
by injectivity on exactly the occurring variable names.
`ForwardQVisibleSpanCapacityIff` derives sharp q≤|V_i| local
root-allocation capacity for full evaluated-span preservation.
`ForwardQGlobalHallSpan` gives the CI-verified finite Hall iff criterion
for simultaneous root-aligned allocation and full tagged global span.
`ForwardQOccurringHallSpan` refines it to actually occurring cone variables,
with unused local names ignored and inside-cone masking explicit.
`ForwardQHallConeData` connects the Hall allocation to the actual
full-frontier three-constructor starred Q-word assembly, conditional on Hall.
`ForwardQCanonicalConeRootChoice` supplies the verified iff criterion
for existence of some old-root transport and a deliberately collapsing
first-visible-root witness.
`ForwardQActualCoordinateWord` samples genuine input coordinate letters
at corrected canonical projected positions across all D₀/D₂ frontiers.
`ForwardQMixedSpanEvaluation` connects actual variable mixed-product
span membership to simultaneous evaluated projected Q-coordinate letters.
`ForwardQProjectedSmoothObservables` characterizes arbitrary Gamma₁/Gamma₂
smoothness by exactly the corresponding observable genuine Q symbols
and fixed Gamma₂ projected nodes.
`ForwardQObservableFingerprint` constructs an explicit quotient record,
whose equality characterizes the same relation and through which
smooth starred colourings factor.
`ForwardQMarkerFingerprint` specializes this record to actual literal
corrected signature marker subsets B₂ ⊆ R.
`ForwardQBulletRootVisibility` establishes nonempty old variable roots at all
actual D₂ frontiers, without inferring the same property for D₀.
`ForwardQStarredOrderReindexObstruction` records the verified
failure of naive printed-to-repaired starred input reindexing.
The TeX audit is intentionally cumulative: older partial TODOs should
be read together with later validation entries.
