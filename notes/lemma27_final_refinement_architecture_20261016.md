# Lemma 27: final ambient refinement without old-root Hall matching

16 October 2026 — standalone mathematical implementation note; corrected
forward-auxiliary convention; source: Todorcevic–Tyros,
*A Dual Ramsey Theorem for Trees*, arXiv:2207.14599v1, pp. 28–29.

## Distinct stages and variable sets

**Stage A, ordinary mixed product:** The paper constructs
Q(w) = (S_w,g_w) for an ordinary starred mixed-product element w,
with concrete ordinary coordinate words w_i. The l variable roots of
g_w are the retained source-interior roots. The already verified
`ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient` proves
syntactic/evaluated refinement of the ambient f with no Hall matching.

**Stage B, a variable subspace:** Applying Corollary 22 yields a
mixed-product variable-word tuple (f_i) (in the printed setting the
up-coordinate family is empty, D = (D0, empty, D2)).
Its independently tagged LOCAL variable roots are (i,z) with
z in ws(f_i). They are NOT a set of variable names of Q(w).
The definition of f' on page 29 explicitly creates variable roots
`P_i(z)` in the original complete support T, and retains the
original f-variables before the distinguished cut.

Therefore an injection from the full family of local tags into the
old l source-interior roots is not implied or required. The separate
`ForwardQOccurringHallSpan` theorems give an exact matching criterion
IF one chooses such an unusually strong encoding; their global
cardinality obstruction is legitimate, but does not contradict
Lemma 27 or replace the f' construction.

## Verified/target geometry

Let I be the forward-sorted outside-cut T frontier indices and
h = k-(m+1), the safe local tail height. Define

    E = Sigma (i : I), b^{<h}
    P(i,z) = projectLocal(c,i,z) in T.

For fixed i, P(i,z) is injective by its certified inverse address

    inverse_T(P(i,z)) = inverse_T(frontier_i) ++ z.

For distinct i, no projected points agree: they lie in disjoint
frontier cones. Hence P is globally injective on E. It preserves
prefixes within each i-cone and never sends a local address to an
old source variable root.

For a genuinely typed mixed variable word f_i, let

    R(f) = union_i { (i,z) : z in ws(f_i) },
    New(f) = {P(i,z) : (i,z) in R(f)}.

The module `DualTree/ForwardQFinalRefinementRoots.lean` packages these
facts, including `New(f) subset T` and disjointness from the retained
old source roots. The full Lean check must pass before these are
recorded as VERIFIED rather than proposed.

## Next exact proof obligations

1. Construct the finite T' as the retained initial support before
   the cut together with New(f), and prove it is an m-dimensional
   forward-complete skew support. Use the mixed variable word's
   vector-complete invariant, the per-frontier canonical prefix
   transport, and rank/ambient-length ordering. The printed formula
   must be adjusted for the existing safe-tail correction.

2. Define the *ambient* word f' uniformly on every fibre of f.
   Before the cut use the original old letter or variable.
   At f-fibres indexed by P_i(z), interpret the local letter or
   map the local variable at z to the NEW variable rooted at P_i(z).
   Outside the selected projected ranges use a fixed original
   letter, as in the printed six cases.

3. Prove f' is root-valid, its support is T', and f' syntactically
   refines f via ONE substitution from ambient f-root names.
   Do not attempt to identify the local variables with the
   source-interior variables of Q(w).

4. Prove the precise family inclusion from the paper:

       [S,f'] subset {Q(w) : w in span((f_i)) and w starred}.

   Ensure that the starred D2 marked points and auxiliary-word
   cases agree, and that the ambient f-fibre locations are used
   rather than an ambient-position cone patch.

5. Only then use the already verified Q-pullback smoothness
   and the mixed Ramsey theorem. Reconcile the printed reverse
   auxiliary order separately; the forward repair does not
   imply a trivial reindexing of the original starred W_* domain.

## Adversarial checks

* A local cone's ambient edge can be stretched; no proof may assume
  P_i(z) is an immediate **ambient** child.
* Independent local names are kept tagged; coincident raw names
  in different coordinates do not identify their projected roots.
* A single old source root can precede many distinct frontiers;
  full old-root Hall matching may fail and is not used here.
* The printed order and corrected order have different starred
  domains; numerical rank conditions must be rechecked.
* The final containment is a statement about f' and Q evaluated
  on a product **span**, not about the full independent tagged
  raw-word span mapped into the old source-interior variables.

No statement here claims Lemma 27 or Theorem 25 is completed.


## Second implementation pass: precise candidate support

`DualTree/ForwardQFinalSupportCut.lean` defines

    Retained(c) = {t in T : ForwardAux(t,cut)}
    Candidate(c,f) = Retained(c) union New(f).

The first set contains the cut and all old source roots, and is
prefix-closed among actual T vertices. Every new projected root
lies strictly OUTSIDE the inclusive cut and cannot prefix an old
retained node. Two new projected nodes from different frontier
indices are mutually incomparable. Therefore the two parts
are disjoint, and Candidate is a finite subset of T.

The complete-skew condition is explicitly NOT claimed. Its
remaining proof must use vector completeness of the chosen local
words, a common safe projection height, and the global corrected
rank/ambient-length order. The proof of f' fibre uniformity and
the family containment are still open. Target: fourteen further
selected Lean axiom endpoints, pending complete CI.


## Third pass: projected-prefix reflection and frontier order

A new `ForwardQFinalProjectionOrder` module (CI pending)
isolates the geometry needed for clauses (ii) and (iii) of the
final T' skewness verification. It proves for any local tails
z,w from one frontier that P_i(z) prefixes P_i(w) iff z
prefixes w. It proves the true rank identity
height_T(P_i(z)) = height_T(frontier_i) + |z|, and transfers
length inequalities |z| <= |w| at increasing frontier indices
i<j to forward auxiliary order and ambient length inequality
of P_i(z),P_j(w). These four transitive-axiom endpoints are
conditional on the local length inequality and do not
infer it from mixed vector completeness yet.


## Fourth pass: the actual vector-complete ordering assumptions

The post-Ramsey mixed variable-word F carries vector-complete
component supports. `ForwardQFinalVectorOrdering` isolates its
two different cross-coordinate clauses: same-intrinsic-level
roots at i<j have nondecreasing local ambient lengths, and
successive local ranks anywhere in the vector have strictly
increasing ambient local lengths. This matches precisely the
conditions of `ForwardQFinalProjectionOrder` needed to
transport forward-order/ambient-length monotonicity across
sorted ambient frontier cones. It does NOT yet prove the
assembled T' is complete skew, since that requires identifying
its OWN intrinsic ranks and connecting its retained initial
cut with the projected supports.


## Essential source-text correction: final height rank budget

The exact printed formula on p.29 selects only local roots z satisfying

    h_ws(f_i)(z) + h_T(frontier_i) < M,

with M the final desired complete-skew height (NOT the Frame
parameter m = h_T(t0), which is the source cut rank m0).
The unfiltered Candidate support formalized in
`ForwardQFinalSupportCut` is an upper envelope, not exact T'.

The proposed `ForwardQFinalHeightBudget` adds:
  * `FitsTargetHeight c f M (i,z)`;
  * `selectedLocalRoots c f M`, a filtered subset of the
    genuinely occurring coordinate support root tags;
  * `selectedProjectedRoots c f M`, the corresponding P_i images;
  * `finalBudgetSupport c f M = retained(c) ∪ selectedProjectedRoots`.

Selected roots satisfy the printed rank criterion by construction,
are still disjoint from the retained old roots, and all lie in T.
Changing M monotonically enlarges the selected support. The
complete-skew proof must use this precise filtered set, not the
unfiltered old candidate. Full CI and axiom validation are pending.


## Fifth pass: predecessor geometry for intrinsic rank

The exact final budgeted support includes retained T-prefix roots
and only local projected roots satisfying the target-height
filter. The proposed `ForwardQFinalBudgetPredecessors` formalizes
the fact that an old retained root precedes P_i(z) exactly
when it precedes the minimal outside-cut frontier t_i;
the predecessor contribution is independent of local z.
Minimal frontier predecessors of T all lie in Retained.
The filter on new roots is downward closed *within the
actual local variable support* and projection preserves
strict local prefixes. Five new audited endpoints, CI pending.

The missing next theorem must COUNT these two disjoint
predecessor families, giving the desired intrinsic rank
height_(T'_M)(P_i(z)) = height_T(t_i)+height_(ws(f_i))(z).
No completeness or global f' claim is being made until then.


## Sixth pass: exact retained intrinsic-height calculation

`ForwardQFinalRetainedRanks` (CI pending) adds generic
rank-versus-predecessor-cardinality lemmas for finite supports,
then identifies every proper ambient T predecessor of a genuine
frontier with a retained old root. Its count is exactly
height_T(frontier_i). It also proves for EVERY retained node s,
even inside the FULL M-budgeted assembled candidate,
height_(T'_M)(s)=height_T(s): no selected projected node
can introduce a new predecessor of s and no retained
T-predecessor is missing.

The full rank equation for new P_i(z) now reduces to counting
the selected projected predecessors in the i-th frontier.
Those should correspond, via strict local prefix reflection
and the hereditary M-budget filter, to the proper predecessors
of z in the local component support. This bijection/cardinality
step is still open, as is M-complete skewness.


## Seventh pass: no extraneous new projected predecessors

The proposed `ForwardQFinalSelectedPredecessors` (CI pending)
makes the new predecessor set EXACT. Different frontier
cones are prefix-incomparable, so any projected root
strictly preceding P_i(z) is P_i(w) with w a strict local
prefix of z, in that very same i-th coordinate. Once
z is selected under the exact target-height bound M,
the downward-closure theorem automatically selects
every such local support predecessor w.

Together with `ForwardQFinalRetainedRanks` this reduces
the full intrinsic height equality for projected nodes
to cardinality preservation of the injective projected
local prefix set. Four selected Lean proof endpoints are
registered, pending CI.


## Eighth pass: cardinality of new projected predecessors

`ForwardQFinalProjectedPredecessorCount` (CI pending)
introduces the bounded local predecessor Finset of z in
the genuine coordinate variable support, proves its
underlying-node image is exactly the local support
strict-predecessor filter, and counts it using duplicate-free
variable supports. The exact new projected predecessor
set is its image under the injective canonical projection
P_i, giving the same cardinality and hence the TRUE local
intrinsic height height_(ws(f_i))(z).

This closes the new contribution to the desired full
rank equation. The remaining gluing lemma must use the
disjoint union of retained and projected predecessor sets
to add old height_T(frontier_i) and the local height.
All complete-skew axioms and final f' word remain open.


## Ninth pass: the complete projected intrinsic-rank equation

The proposed `ForwardQFinalIntrinsicRank` (CI pending)
splits all strict predecessors of P_i(z) in the EXACT M-filtered
support into (1) retained T-predecessors and (2) selected
projected local support predecessors. The disjointness
lemma for the two support pieces makes their cardinalities
add, yielding the precise intrinsic rank identity

    height_(T'_M)(P_i(z))
      = height_T(frontier_i) + height_(ws(f_i))(z).

The rank-budget inequality from the original Lemma 27 formula
then proves all selected new projected support roots lie at
intrinsic final-support rank strictly below the target M.
Rank preservation for retained vertices was validated in
`ForwardQFinalRetainedRanks`.

Full M-complete skewness is NOT an automatic consequence:
the corrected proof must still check unique full branching,
relative rank/length order including retained/new comparisons,
and appropriate M versus old cut-rank parameter bounds.
Then one must build the actual full ambient variable word f'.


## Tenth pass: uniform actual intrinsic target-rank bound

The proposed `ForwardQFinalRankBound` (CI pending)
combines the complete T's corrected forward-order/rank
monotonicity with rank preservation for retained vertices.
Every retained t at/before cut has final rank at most
height_T(cut)=m0, and under the explicit numerical
hypothesis m0<M this is strictly below target M.
The separately proved formula for every selected P_i(z)
yields the same strict <M bound for NEW roots from the
printed target-height filter. The union yields
height_(T'_M)(s)<M for ALL support vertices.

This does not prove full M-COMPLETE skewness:
full immediate support branching and all ordering axioms
still require the exact support geometry; afterward the
final f' word/refinement and Q-span containment remain open.


## Eleventh pass: the indispensable rank-m versus rank-(m+1) split

For the actual Corollary 22 dimension q=M-m and original cut
rank m, a minimal corrected frontier f_i has ambient T-rank
either m or m+1 (checked in `ForwardFrontierRanks`).
Its proper local projected roots must satisfy

    height_(ws(f_i))(z) + height_T(frontier_i) < m+q.

The proposed `ForwardQFinalTwoFrontierBudget` proves:
- if height_T(frontier_i)=m, EVERY local variable support root
  is selected; its local height is automatically <q;
- if height_T(frontier_i)=m+1, selection is EQUIVALENT to
  membership in the local support plus local height+1<q;
- q<=1 therefore selects NO roots from the upper frontiers.

The latter is not a counterexample; the earlier cut at rank m
is already a permissible terminal level if M=m+1.
Any complete-skew gluing proof must respect this precise
one-level height discrepancy across frontiers.


## Twelfth pass: selected local roots exist where needed

A q-complete coordinate support f_i has a unique common prefix
root z_i of local intrinsic height 0, even in the singleton
case. The proposed `ForwardQFinalLocalRoots` supplies a
genuine bounded variable-root witness z_i, and proves its
projection P_i(z_i) is selected by the exact target M=m+q
budget whenever the frontier has T-rank m; the same holds
for frontiers of rank m+1 when q>=2. The exceptional q=1
upper-frontier case correctly remains empty. These witnesses
are an essential input to the retained/nonleaf branching
proof; full branching in every direction is not yet shown.


## Thirteenth pass: full local branching under the two cutoffs

The proposed `ForwardQFinalLocalBranching` (CI pending)
uses actual q-completeness of each f_i support to show:
at every local rank r with r+1<q, there is a unique
immediate local SUPPORT successor in each ambient
direction, and its local intrinsic rank equals r+1.
At a rank-m ambient frontier, this successor belongs to
the selected exact T'_M support. At rank-(m+1)
frontiers, it belongs to that support under the
stronger r+2<q condition. This accounts for the
one-level shorter upper-frontier truncation.
The remaining nonlocal gluing theorem must prove
these become the actual immediate T'_M successors
and verify the retained/new branching interface.


## Fourteenth pass: immediate local edges in the full glued support

The theorem `ForwardQFinalImmediateGluing.selected_local_immediate_is_final_immediate`
(CI pending) proves that for a selected local immediate edge z -> w,
the ambient projections P_i(z) -> P_i(w) are immediate in the FULL
T'_M support. A retained vertex cannot intervene after the cut;
a projected intermediate is forced into the same coordinate and
reflects to a forbidden intermediate local support vertex.
This checks one source-facing endpoint. The exact ambient direction
of this projected edge, initial retained/new branching,
and M-complete skewness are still open.


## Fifteenth pass: labelled direction transport (rebased)

`ForwardQFinalProjectionDirection` (CI pending) checks the
labelled first-child cone for the genuine corrected
forward-complete canonical embedding, using its intrinsic
support-rank budget and directional CanonicalSupportWalk.
After substituting the certified inverse-address formula
for each P_i, it proves local child-direction cones are
sent to the SAME ambient direction cones.

This result is independent of abstract prefix-order preservation:
a generic prefix isomorphism can permute the sibling labels.
In conjunction with merged immediate edge gluing, it supports
constructing the actual b directional immediate successors
of sufficiently early projected vertices of T'_M. The retained
cut interface must still be proved.


## Sixteenth pass: immediate directional successors in glued T'_M

`ForwardQFinalProjectedFullDirections` (CI pending)
combines four carefully separated facts:
(1) a strict local support prefix edge with rank difference one
is immediate, even in a stretched ambient tree;
(2) local q-completeness supplies an immediate child in
each requested ambient direction at early intrinsic levels;
(3) selected local immediate edges remain immediate
in the FULL T'_M after gluing; and
(4) the actual canonical projection preserves the
first ambient direction label.
Thus early selected NEW roots have actual immediate
T'_M support successors in every direction.
The exact height slack is r+1<q for rank-m frontiers,
and r+2<q for rank-(m+1) frontiers.
The retained/new interface, uniqueness of other
successors per direction, global skew order, and
final ambient f' remain open.


## Seventeenth pass: immediate edges from retained old support

`ForwardQFinalRetainedEdges` (CI pending) proves two
cases for an ambient T immediate support edge s->t from
a retained parent s. If t is retained then the edge
remains immediate in the entire glued T'_M, because
T-immediacy forbids other retained intermediates and
selected projected nodes never prefix a retained node.

If t is outside the inclusive cut, then t itself is a
minimal outside-cut T frontier, whose rank is m or m+1.
Thus there is no need for a new arbitrary frontier
choice: the last retained edge determines its frontier
uniquely. The remaining retained/new gluing lemma should
take the local root z_i of the corresponding mixed
coordinate support f_i, prove P_i(z_i) replaces the
outside endpoint t, and establish immediate adjacency
plus its old ambient direction from s.


## Eighteenth pass: immediate retained/new edge from rank-gap equality

`ForwardQFinalRetainedFrontierGluing` (CI pending)
uses the exact intrinsic rank formula for the target-filtered
support: the projection P_i(z_i) of the local component
ROOT has local summand zero and therefore has final height
equal to height_T(frontier_i). When frontier_i is
immediate in ambient T above retained s, this is
height_T(s)+1 = height_(T'_M)(s)+1.
The shared prefix relation and the generic rank-gap
criterion imply that s→P_i(z_i) is IMMEDIATE in the
whole T'_M, preserving the original outgoing ambient direction.

This replaces a large and redundant intermediate-vertex
classification in the retained/new proof. The next step
is the sorted-frontier index lookup for every crossing
ambient immediate edge and selecting z_i at rank m or m+1.
Global M-complete skewness and final f' remain open.


## Nineteenth pass: remove the sorted-frontier-index premise

`ForwardQFinalRetainedCrossing` (CI pending) proves that
an immediate ambient T-edge crossing from retained s
to an outside-cut t lands at an ACTUAL sorted frontier
index i, with t=frontierAt(i). No arbitrary index or
relabeling of coordinate words is required. Under the
natural early-retained bound height_T(s)+1<M=m+q,
the q-complete component's genuine local root z_i is
selected. In the upper rank-(m+1) case, the bound
forces q>=2; in the lower rank-m case all local
roots survive. The rank-gap gluing lemma therefore
supplies an immediate T'_M edge s→P_i(z_i)
in the original requested ambient direction.

The retained-vertex full-direction EXISTENCE theorem
now reduces to taking the actual directional immediate
T-successor and splitting on whether it is retained.
Full uniqueness, global skew order and the final f'
construction are still open.


## Sixteenth pass (17 October): every early retained root has a directional successor

`ForwardQFinalRetainedFullDirections` (CI pending)
eliminates the last preselected-crossing-edge premise:
for every retained root s of final rank r with r+1<M=m+q
and requested ambient direction j, the original k-complete
T has a unique immediate T-successor in direction j
provided the explicit capacity M<=k holds.
It either remains retained, yielding the same immediate
T'_M edge, or crosses the inclusive cut; in the latter
case `ForwardQFinalRetainedCrossing` supplies the actual
sorted frontier index and selected projected local-root
replacement in exactly the same direction. Hence the
branch-witness list of T'_M at s,j is nonempty.

This proves directional EXISTENCE, not uniqueness. A
second theorem must rule out competing immediate successors
in a given direction, ideally via meet-closure of T'_M
(or an equivalent local-on-projection predecessor argument).
The numerical capacity M<=k must be justified from the
actual local q-complete word's ambient tail height before
the manuscript uses this result without assumptions.


## Seventeenth pass (17 October): actual q-complete input bounds the final height

`ForwardQFinalMixedCapacity` (CI pending) derives the previously
explicit m+q<=k capacity assumption from every ACTUAL mixed
coordinate. A q-complete component has a terminal local
root of rank q-1. The number of distinct strict support
prefixes of any ambient word is at most its ambient length:
their lengths are distinct and smaller than |z|. Since local
variable roots live in bounded tails of height k-(m+1),
the terminal's intrinsic level forces q<=k-(m+1)
and thus m+q<=k.

The coordinate premise cannot be dropped for an empty
mixed product, where vector-completeness is vacuous.
Discharging the retained-direction capacity in the global
statement requires either a real sorted frontier index
or an outgoing-branch witness that yields such an index.
Afterwards the two completeness difficulties are
uniqueness of same-direction immediate successors
and the global skew order/length clauses.


## Eighteenth pass (17 October): unconditional retained directional existence

`ForwardQFinalRetainedUnconditional` (CI pending) proves
that a requested direction at the distinguished cut
produces a genuine ambient T immediate successor of
rank m+1. This successor lies outside the inclusive
forward cut, and the existing sorted-frontier theorem
gives an actual local mixed-product coordinate i.
The q-complete bounded coordinate word forces m+q<=k,
discharging the only added numerical premise.

Therefore EVERY retained vertex whose final intrinsic
rank r satisfies r+1<m+q has a genuine immediate final
T'_M successor in each requested ambient direction.
No preselected frontier index and no independent
capacity bound remain. The remaining structural
obligations are SAME-DIRECTION UNIQUENESS, the skew
level/length clauses and full last-level branching
classification, before constructing final f' and
the span-containment statement of Lemma 27.


## Nineteenth pass (17 October): all low-rank final-support nodes branch in every direction

The proposed `ForwardQFinalAllDirectionExistence` (CI pending)
combines the actual retained-root full-direction theorem
with the projected-root geometry. At a selected P_i(z),
the checked final rank is height_T(frontier_i)+localRank_i(z).
When this final height plus one is below M=m+q, the
corrected frontier height band {m,m+1} gives exactly
the local height inequalities already established in
`ForwardQFinalProjectedFullDirections`. Therefore each
selected new vertex receives a genuine IMMEDIATE edge
in every requested ambient direction in the entire
filtered final support. Retained vertices are handled
by `ForwardQFinalRetainedUnconditional`.

Consequently, for ANY s in T'_(m+q) with final rank
r and r+1<m+q, all branchWitnesses lists are nonempty.
This is the EXISTENCE half of global b-branching.
The at-most-one-per-direction theorem is still needed;
it will likely follow from ambient meet-closure of T'_M
or equivalent predecessor/branch splitting geometry.
Global skew order and full last-level leaf verification
are also open.


## Twentieth pass (17 October): converses for retained immediate children

The proposed `ForwardQFinalRetainedChildConverse`
(CI pending) proves:
1. every immediate final support edge between retained
   vertices was immediate in original complete T;
2. if a retained s has immediate selected projected
   child P_i(z), its actual frontier_i was immediate
   above s in T and its local z has rank zero;
3. any rank-zero vertex of a genuine q-complete
   coordinate support equals its unique localRoot.

So all final immediate children from retained parents
are either old ambient T immediate children still
retained, or the UNIQUE root projection replacing a
cut-crossing ambient T immediate child. The remaining
retained-vertex at-most-one-direction statement should
follow from uniqueness of that original T successor
per direction, with the selected projection replacing
an outside child. The projected-parent uniqueness
case will be treated separately.


## Twenty-first pass (17 October): projected final children are exactly local immediate children

The proposed `ForwardQFinalProjectedChildConverse`
(CI pending) classifies all immediate children of
a projected selected P_i(z) in the WHOLE filtered T'_M.
The child must be a selected projection P_i(w) in the
same frontier (no retained or differently labelled
frontier can occur), with a strict local prefix z<w.
The final intrinsic rank gap of this immediate edge
equals one, and the checked projected-final height
formula cancels the common ambient frontier rank,
yielding localRank(w)=localRank(z)+1. Thus z->w is
a genuine LOCAL immediate support edge.

Together with the already checked direction-labelled
projected cone map, this should imply same-direction
uniqueness at selected projected vertices from
the local q-complete support's unique directions.
The retained-parent case uses the separate converse
classification of retained children.


## Twenty-second pass (17 October): projected first direction is an equivalence

The proposed `ForwardQFinalProjectionDirectionReflect`
(CI pending) proves the exact labelled first-direction
equivalence z++[j] prefix w iff P_i(z)++[j] prefix
P_i(w). Prefix reflection extracts the local suffix;
the suffix is nonempty when the projected first-child
cone is strict, and its initial local direction is
carried unchanged by the previously verified projected
direction-preserving theorem. Equal-length uniqueness
forces the local and projected first directions to agree.

This prepares direct reuse of local q-complete
uniqueBranchB to prove at-most-one projected immediate
child per ambient direction in the WHOLE selected
T'_M support, using the projected-child converse.


## Twenty-third pass (17 October): unique directions at every selected projected parent

The proposed `ForwardQFinalProjectedDirectionUniqueness`
(CI pending) establishes the at-most-one-direction
property for immediate final children of ANY selected
projected P_i(z), independent of its final height.
All such children are images of local immediate
support edges in the SAME coordinate i (checked
converse). Their actual first direction j is
reflected by the corrected projection back to
the local support. The q-complete local support is
meet-closed when nonsingleton, and the generic
meetClosed=>AtMostOneDirection theorem prohibits
two distinct local immediate children in j.
Therefore the final children coincide.

The remaining uniqueness case has a RETAINED parent:
each final immediate child then determines a genuine
immediate original T child, either retained unchanged
or replaced by the actual selected frontier root.
Uniqueness in original T should finish that case.


## Retained-parent uniqueness rebase after projected-parent audit

`ForwardQFinalRetainedDirectionUniqueness` (two selected
endpoints, refreshed PR #346, CI pending) reduces EVERY
immediate successor of a retained final vertex to the
corresponding actual T-immediate edge in the same first
ambient direction. This uses the retained-child converse:
the final child was either unchanged retained, or a projected
local root replacing a minimal outside-cut frontier. Unique
ambient directions follow from meet closure of original
complete T; mixed retained/projected cases contradict the
inclusive cut, while two projected cases share the same
sorted frontier and the canonical localRoot choice.

The projected-parent at-most-one-direction theorem is
now verified on main through #345. This retained theorem
would finish all-parent at-most-one-direction. It does
not by itself establish complete-skew length order,
the last-leaf rank condition or the final ambient word.


## Eighteenth pass: exact early branching in final T'_M

The proposed `ForwardQFinalExactBranching` (four
selected endpoints; stacked after retained-direction
uniqueness PR #346; CI pending) constructs a global
AtMostOneDirection theorem by cases on the *actual*
retained/projected decomposition of the final support.
A generic duplicate-free finite-list lemma converts
nonempty branchWitnesses plus AtMostOneDirection to
uniqueBranchB. The checked all-vertex existence theorem
therefore gives uniqueBranchB in every direction at
all ranks satisfying h_(T'_M)(s)+1<M; the previously
verified direction-count equivalence then yields
exactly b immediate support successors at every such
vertex.

This is the full EARLY-BRANCHING numerical clause.
To claim M-complete skew still requires showing every
last-level node is a leaf, establishing the global
forward auxiliary-order length conditions (ii)/(iii)/(iv),
and constructing the genuine ambient variable word f'.


## Nineteenth pass: all leaf/branch count clauses

`ForwardQFinalLeafBranchClause` (three selected endpoints,
stacked PR, CI pending) proves a vertex at final
intrinsic level M-1 cannot have an immediate successor:
the successor would have height M, contradicting
the exact all-vertex rank bound in T'_M. Conversely
the full existence + uniqueness chain proves
each earlier vertex has exactly b immediate successors.
For positive branching b and positive new depth q,
the completeB branch/leaf Boolean conjunct is
therefore verified. The module exports the conditional
equivalence between M-completeness of T'_M and the
independent remaining skewB predicate (corrected
forward auxiliary order).

This is not a proof of skewB. Its rank-versus-ambient
length clauses and special witness condition still
need formalization; the final ambient f' word and
Q-span containment remain open.
