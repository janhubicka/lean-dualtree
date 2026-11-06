# Track B: genuine height-one D1 leaves and mixed spans

Continuation of the `T A` split, issue [#515](https://github.com/janhubicka/lean-dualtree/issues/515).
Starting baseline: `910efe61e94a284be065f4a782bec878c5d1170f`, including
the merged Track A dependencies #512 and #513. The validation branch is
integrated with `4306242fc876b0ddc03143caea8a3abc433568d9`, including
Track A's nonempty, interleaved no-D1 height-one result (#529). This work adds `UpLeaf*`
modules and the associated regression/axiom registrations. It does not change
the Track A constructions or the Q definitions.

## Statement correspondence and scope

`MixedProduct.VariableWord` requires, at each actual D1 coordinate, a
duplicate-free list of exactly `b^k` nodes at **ambient level n**, with a
skew extended support. At `k=1`, the new construction supplies exactly `b`
such leaves above a specified bounded singleton support root.

For `0 < b`, `|r| < n` and `j : Fin b`, put

\[
  \ell_r(j)=r\mathbin{{}^\frown}(j)
    \mathbin{{}^\frown}0^{n-|r|-1}.
\]

The public functions `UpLeafGeometry.ambientLeaf` and `ambientLeaves` use
this formula. The type of `r : BoundedNode b n` carries the strict bound
`r.length < n`; the result has type `MixedProduct.LeafNode b n`, which
requires exact length `n`.

The more general theorem permits an arbitrary level-n extension in each
direction, with no restriction on its tail:

```lean
theorem DualTree.UpLeafGeometry.star_skew
    {b n : Nat} (hb : 0 < b)
    (aux : Node b → Node b → Bool)
    (r : Node b) (leaf : Fin b → Node b) (hr : r.length < n)
    (hlen : ∀ i, (leaf i).length = n)
    (hbranch : ∀ i, IsPrefix (r ++ [i]) (leaf i))
    (haux : ∀ i, aux (leaf i) r = false) :
    SkewTree.skewB aux (UpLeafGeometry.star r leaf) = true
```

The `haux` condition is discharged for both `SkewTree.paperAuxB` and
`SkewTree.forwardAuxB`. Thus this height-one leaf result is valid for both
auxiliary orders and does not rely on a proposed repair of Q.

## Proof of the leaf geometry

Distinct directions give distinct leaves: a node cannot extend two different
immediate successors of `r`. The root is shorter than every leaf, so adjoining
it creates no duplicate. The only predecessor of a selected leaf in the
extended support is `r`; every selected leaf is terminal. Consequently the
root has intrinsic height zero and every leaf has intrinsic height one.

These facts verify both length clauses: equal-height leaves have equal
ambient length, and the root is strictly shorter. The immediate successors
of the root are exactly the selected leaves, with one successor in each
direction. The root and the last direction witness clause (iv). The only
auxiliary-order requirement in this argument is that a terminal leaf cannot
lie before the root and therefore be required to branch.

The proof checks the existing executable `skewB` predicate in full. It does
not replace it with meet closure or componentwise branching alone.

## Genuine mixed words and exact spans

`UpLeafMixedWord.attach` takes any existing vector of genuine height-one
variable words whose component support lists are the specified singletons.
It preserves the whole vector-completeness certificate and adds the actual
leaf lists at every D1 coordinate. Repeated occurrences of the sole variable
are allowed. `attach_span_nonempty` constructs an actual span element from
a supplied alphabet letter; nonemptiness is a conclusion.

`UpLeafMixedWord.mixedWord` supplies a concrete such vector for any kind
function `Fin d → CoordKind`. Its bounded roots must have weakly increasing
ambient lengths in coordinate order, exactly the requirement used by the
existing singleton-vector theorem. At each coordinate its variable occurs
at the root, and all other positions carry the supplied fallback letter.

Its span has the following exact, injective parameterization:

\[
 (a,\delta)\in \alpha^d\times
       \prod_{i\in D_1}\{0,\ldots,b-1\}.
\]

Coordinate `i` has root letter `a(i)`. Each D1 point is the actual leaf
`ambientLeaf hb (roots i) (δ i)`. Each D2 point is its actual singleton
support root. The forward membership theorem, converse representation,
range equality and injectivity are all separate endpoints. In particular,
there is no coupling between different coordinates' letters or leaf choices.

The explicit existence bound is:

```lean
theorem DualTree.UpLeafMixedWord.exists_mixedWord_nonempty
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (hn : 0 < n) (kind : Fin d → CoordKind) (a : α) :
    ∃ f : MixedProduct.VariableWord b n d 1 α SkewTree.forwardAuxB kind,
      f.span.Nonempty
```

Height one suffices for this geometric existence statement: all roots may
be empty. This is **not a Ramsey bound**. `UpLeafExamples.threeWord` also
gives a D0/D1/D2 fixture at ambient height three, with distinct root lengths
0, 1 and 2, and an actual independently varying up coordinate. Its distinct
direction theorem verifies that different branch choices remain different
span elements.

## Canonicalization interface

For the concrete parameter family, equality of the Lemma-14 `SameUpTrace`
record is equivalent to agreement of:

1. the selected direction at each D1 coordinate;
2. the root letter at each D1 coordinate.

The D0 and D2 root letters are absent from this record. The theorem
`upCanonical_iff_parameter_constancy` therefore states the exact remaining
color-invariance condition on the other letters, at fixed D1 data.

When **every coordinate is D1**, the trace determines the entire actual
span element. Hence `upCanonical_allUp` proves `UpCanonical` for every
coloring on the concrete height-one word. The stronger
`upCanonical_attach_allUp` proves the same result for any singleton-supported
vector passed to `attach`, including repeated variable occurrences. This
uses equality at the unique root to determine the whole evaluated word.

For Definition 11, `good_iff_parameter_bullet_constancy` gives a different
exact criterion: the induced color must depend only on the D2 root letters.
All D0 and D1 letters, and all D1 directions, must be erased. The equivalence
exposes this unresolved combinatorial input; it does not assume or conclude
that every coloring already has it.

## Adversarial boundaries

- Correct cardinality, distinct leaves and rootedness do not suffice.
  The binary leaves `00,01` above the empty root miss direction 1 and fail
  the actual skew predicate under both orders.
- Leaves outside the root cone fail rootedness.
- At equal height, the unary leaf repeats the root; the strict height gap
  is essential.
- The raw mixed-word definition permits `b=0`. An actual one-up word with
  a nonempty alphabet then has an empty span. The positive construction
  explicitly assumes `b>0` and supplies an alphabet letter.
- A genuine binary one-up word at the empty root, with leaves `0,1`, is
  not `Good` for the color that observes its selected branch. This is a
  counterexample to automatic goodness of **prescribed geometry**, not to
  a Ramsey theorem allowed to choose a different root at greater height.

`scripts/check-up-leaf-geometry.py` exhaustively checks all 8,700 ordered
leaf-list cases for `b=1,2`, `n=1,...,4`, all bounded roots, and both auxiliary
orders. Lists with repeated entries are included. In this finite domain,
skewness is equivalent to choosing exactly one representative in each root
direction. The general Lean theorem establishes sufficiency; the finite
equivalence is a regression result, not a claimed general converse theorem.

## Validation and remaining work

The new endpoints are registered in `scripts/CheckDualTree.lean`; the full
Lean workflow includes the new finite regression and the existing skew/Q,
TeX, import-graph and transitive-axiom gates. Exact CI head/status is recorded
in the accompanying pull request. Source compilation and CI completion must
be checked before treating these source files as validated.

The Track B definition of done concerns actual k=1 support-and-leaf geometry,
explicit bounds, nonempty span and the complete CI gate. The broader mixed
Ramsey theorem remains separate: choosing the support and leaves in response
to a coloring, handling interleaved D0/D1/D2 canonicalization, and extending
the construction to `k≥2` require further work. No Q or final-theorem blocker
is discharged by the present height-one geometry.
