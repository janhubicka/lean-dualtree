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
