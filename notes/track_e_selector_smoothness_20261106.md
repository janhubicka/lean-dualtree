# Track E: canonical semi-complete selector and simple-to-smooth transfer

Date: 6 November 2026. Task: [#518](https://github.com/janhubicka/lean-dualtree/issues/518).
Base: `910efe61e94a284be065f4a782bec878c5d1170f` (main after #512 and #513).

## Result and scope

The new construction defines and validates the canonical selector on **every
eligible forward-order semi-complete starred tree**, including zero interior.
It does not require that the tree be a Q image or extend to a complete tree.
It then supplies a source-independent corrected Definition-24 simplicity
predicate and its total smooth Q pullback, without selector-agreement,
root-law, successor-law, or model-admissibility hypotheses.

All statements explicitly use the corrected forward auxiliary order. They
are not an identification of the printed reverse-order domain with this
corrected domain. The source-order repair and the Q/refinement problems
listed in Track D remain separate.

## Source comparison and explicit correction

In [Todorcevic--Tyros, arXiv:2207.14599v1](https://arxiv.org/pdf/2207.14599),
Section 3.1.2 (page 8) defines the canonical isomorphism only for a complete
skew tree. Definition 24 (page 26) uses the same notation on semi-complete
trees and separately specifies the zero-interior boundary. The corrected
definition needs the following extension, with the auxiliary order fixed
consistently to the forward convention used by the corrected Q construction.

Let `H_l` be the first `l` homogeneous addresses in forward breadth-first
order. For positive `l`, let `A_l` be the children of `H_l` outside `H_l`;
for `l=0`, set `A_0={[]}`. Given a semi-complete starred support `U` with
`l` interior vertices, define `I_U([])` to be the root of `U`. For each
`p` in `H_l` and direction `i`, define `I_U(p++[i])` to be the unique
immediate **support** successor of `I_U(p)` in direction `i`.

The new theorems establish that this recursion is defined on the whole
model `H_l ∪ A_l`, is independent of a source frame, and is a bijection
onto `U`. It preserves and reflects prefix, lexicographic, and forward
auxiliary order. It sends `H_l` exactly to the interior and `A_l` exactly
to the leaves. Its model addresses have length below the given ambient
height. Thus taking the boundary inside the finite homogeneous tree,
as Definition 24 does, agrees with the unbounded-address formalization
whenever an eligible `U` exists.

The underlying walk is totalized outside this model, but the new
admissibility theorems show that none of its fallback transitions is used
on the canonical model. At `l=0` every vertex of `U` is its root, so the
special boundary convention selects the unique genuine leaf.

## Proof structure

1. `ForwardSemiCompleteAddresses` proves, directly from `U`, that every
   interior vertex has a unique support successor in each direction.
   Admissible directional addresses are in bijection with all vertices;
   address length equals intrinsic height.
2. `ForwardSemiCompleteAddressOrder` proves preservation and reflection
   of all three tree orders. Singleton supports are handled separately
   where the raw skew definition does not impose the nonsingleton clauses.
3. `ForwardSemiCompleteInitial` chooses a maximal interior vertex only
   inside the proof. The full-before skew axiom makes the interior an
   initial segment. Strong induction on the heap address proves that
   no smaller addresses are missing. Comparing exact cardinalities then
   identifies this segment with `H_l`. The final theorem has no chosen cut
   in its assumptions.
4. `ForwardSemiCompleteBoundary` follows one real successor from each
   model-interior parent and proves the exact all-`l` leaf bijection.
   Its converse uses the last direction of the leaf's own admissible
   address, rather than an arbitrary enumeration of leaves.
5. `ForwardSemiCompleteModelIso` assembles the complete finite-model
   isomorphism and its root/successor uniqueness criterion.
6. `ForwardSemiCompleteSimplicity` defines the selector and simplicity
   without a Q frame, cut, source signature, or marker set, and proves
   their exact correspondence to the existing corrected Q interface.

## Colour transport

For an ambient variable word `f`, a starred refinement means exactly
that its tree is contained in `f`'s support and its word span is contained
in `f`'s span. `SimpleWithin f B2 color` compares **all** such starred
refinements having the same interior, the same canonical points at `B2`,
and the same rooted word symbols outside the inclusive cones at those
points. `Simple f color` existentially quantifies the partition subset
`B2`; its complement is `B1`.

The new source-independent predicate is equivalent to the existing
intrinsic-selector `CanonicalSimpleWithinAmbient`, not merely a condition
on Q images. On actual corrected Q outputs its canonical boundary points
are proved to be the real projected D2 markers. Transporting `B2` through
the canonical boundary-to-D2 equivalence gives exactly the Γ2 coordinates.

Consequently `simpleWithin_Q_pullback_smooth` proves smoothness on the
genuine enlarged starred input domain, and
`exists_total_simpleWithin_Q_pullback` extends that same pullback to a
total smooth colour function on the whole enlarged mixed product. The
existential-partition version is `simple_exists_total_smooth_Q_pullback`.
The total extension requires an explicit default colour on classes not
meeting the starred domain. Actual Q frames necessarily have positive
interior; the all-`l` selector theorem does not fabricate a zero-interior
Q frame.

## Γ1 audit and remaining work

Existing main already proves Γ1 encoder extensionality at a fixed
projected point from equality of the rooted target symbol
(`ForwardQFinalEncoderExtensional.encodeProjectedOutputSymbol_eq_of_rootLabel`).
It uses equality of the choice predicates, not injectivity of the auxiliary
decoder. Existing reduced-record factorization and its total extension
remain conditional on the appropriate genuine smooth/c-good inputs.

Different retained Γ1 letter tuples are **not** identified. The checked
counterexample in `MixedGoodSmoothRecordObstruction` remains in force:
c-goodness does not make the complete residual record constant. This
work does not assert such constancy, produce a higher-dimensional Ramsey
witness, repair Q span/refinement, or complete Lemmas 27--28 or Theorem 25.

The corrected selector and colour-transfer statements are the Track-E
output for integration. Their use in the original theorem still requires
an explicit source-order correction and the independent construction
and induction inputs in Tracks A--D and F.

## Validation

Validation is in progress. The final report must record compilation,
the complete source and transitive-axiom checks, finite regressions,
and the exact reviewed PR head; source text alone is not a Lean check.
