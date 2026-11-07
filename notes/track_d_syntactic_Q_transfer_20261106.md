# Track D: source-relative syntactic Q transfer

**Date:** 6 November 2026. **Starting main:**
`910efe61e94a284be065f4a782bec878c5d1170f`, through merged PR #513.
**Assignment:** issue #517, `track-d/q-span-refinement`.
**Integrated main:** `b985bfee976cb682142986579de0f4680d7e6400`,
including Track A PRs #522, #523, #524, #525, and #529, and the
completed Track E selector work in PR #526 and Track B D1 geometry
in PR #530.

## Exact scope and the corrected inclusion

The existing development already handles genuinely fixed auxiliary
constants in the local alphabet `α ⊕ Fin(m+1)`, reconstructs eligible
target words at every ambient position, and derives their corrected D₂
order from target geometry. Those results are reused here.

The required inclusion is an inclusion of **fixed-signature starred
targets**, retaining both their tree and their variable-word symbols:

\[
 \operatorname{observe}([\mathcal S,f']_{\mathrm{syn}})
 \subseteq
 \{\operatorname{observe}(Q(w)):w\in[f]_{\mathrm{mixed}}\cap W_*^{\mathrm{fwd}}\}.
\]

Here `f` denotes the local mixed word, while `f′` denotes the final
ambient interpolation. The independent ambient refinement has direction
`span(f′) ⊆ span(ambient)`. No unrestricted reverse inclusion for the
constant evaluated span of `f′` is claimed. The retained-root obstructions
to that different assertion remain valid.

`SourceRelativeSetTarget` specifies the bracketed class exactly:

1. The target has the same **complete corrected forward signature** as
   the source, with its target cut explicitly quantified. The signature
   tree is its finite node set; the rooted partial word includes its
   full strict initial domain.
2. Its word is a uniform syntactic substitution of the final word.
3. Every vertex of its tree, including its terminal leaves, belongs to
   the final word's actual support.

The third condition does not follow from word substitution: the word's
variables describe interior roots, and do not alone control terminal
tree vertices. It remains explicit throughout the theorem.
The earlier `SourceRelativeTarget` interface, which additionally fixes a
literal signature-tree list enumeration, remains available as a stronger
special case with its existing theorem types.

## Why syntactic refinement matters

The new source relation is

```lean
SyntacticallyRefines target source :=
  ∃ ρ : source.Vars → Sum α target.Vars,
    target.word = SpanAudit.substitute source.word ρ
```

It preserves constants, equality of source symbols, and entire variable
fibres for every alphabet. Every surviving target root is an actual source
root. The substitution is
uniquely determined by reading the target symbol at each source root.
Thus the source fibre frame can be built canonically from the actual
ambient word, full-node support correspondence, and source refinement.
The ambient boundedness and substitution fields are derived.

For an alphabet with two distinct letters, the relation is equivalent to
evaluated-span inclusion. For a singleton alphabet, evaluated spans lose
variable names and root locations. The new theorem therefore assumes
the syntactic relation directly and needs no `HasTwoLetters α` premise.
All pre-existing two-letter span theorems retain their original types as
corollaries of the symbolic versions.

The singleton regression uses the existing actual binary-tree root word
and left-child word at every ambient height at least two. Both have
1-complete skew support and equal evaluated spans, but the left-child
word cannot syntactically refine the root word. A separate genuine
unary identity instance has complete support and nonempty span.

## Construction and proof

The local symbol proofs are generalized in three cases. Original
constants are preserved by substitution. Fixed auxiliary constants
are decoded by the actual `R_i`; when the decoder names an old variable,
the complete-signature root correspondence and the target's root law
force that same rooted variable. A local variable receives one uniform
enlarged letter on its entire fibre. Composing the target substitution
with the actual final-to-ambient substitution extends the identity to
every original ambient fibre and hence every bounded position.

No occurrence-Hall or retained-root matching premise is needed by this
construction. The actual source fibres and complete signature determine
the old-root correspondence, while selected local variable tags have
their genuine injective projections. The earlier conditional Hall
lemmas and unrestricted reverse-coverage obstructions are retained.

The target's tree reconstruction and automatic D₂-order proof are
unchanged. They promote this actual mixed-span input to the corrected
starred subtype. The resulting Q word has the target's complete
tree-and-rooted-word observation; tree enumerations are compared by
permutation, never by an unjustified literal list equality.

The finite-set signature is connected to the existing literal interface
by an actual re-enumeration proof. Equal full partial-word domains first
force the same cut. At that cut, signature nodes at or before the cut
are precisely the original interior nodes, and the remaining signature
nodes are precisely the exceptional first boundaries. Thus equality of
signature node sets gives equal interior membership and a bijection of
exceptional leaves preserving their first-boundary nodes. Injectivity of
the genuine boundary maps is supplied by the existing source-frame
geometry. The target's containment in the ambient support, needed to
construct its frame, follows from its final-support containment.

Enumerate the target as the source's interior list, then its exceptional
leaves in the matched source order, then its leaves below the cut. This
is a permutation of the original target tree. Its interior and mapped
exceptional-boundary lists agree literally with the corresponding source
lists, so the signature's final duplicate removal gives the same list.
The target's entire variable word is unchanged definitionally, and its
complete observation is unchanged. The old literal Q transfer therefore
applies without imposing a choice of enumeration on the external target.
`ForwardQFinalSetSignature`, `ForwardQFinalStarredReenumeration`, and
`ForwardQFinalSetSignatureReenumeration` contain these bridges.

The final interpolation is now also packaged as an actual
`KVariableWord b n (m+q) α forwardAuxB`. Its bounded support enumeration
may differ from the enumeration used by the previous completeness
proof. A permutation-invariance lemma for `SkewTree.completeB`
transports intrinsic heights, successor counts, and skew clauses to
the actual word support. The underlying interpolation is unchanged
definitionally. Positive branching and positive local height are
explicit. A constant assignment gives a real nonempty evaluated span.

The relative refinement also retains **every** original ambient support
root at or before the forward cut, including roots outside the old
starred source-variable support. The retained part of the final support
gives this directly. The actual substitution and the existing cut
preservation theorem then identify constants and rooted variable symbols
at every bounded position in the inclusive initial segment. Both facts
hold without an alphabet-cardinality or positive-local-height hypothesis.
They are exposed in `ForwardQFinalInitialRootRetention` and included in
the main assembly theorem, matching the root-retention requirement of
the paper's Definition 26 in the corrected forward order.

The assembly theorem is

```lean
ForwardQFinalSetSpanTransfer.
  exists_complete_set_source_relative_Q_transfer
```

Its inputs are the corrected source fibre frame, a genuine enlarged
local mixed variable word, a fallback original letter, `0 < b`, and
`0 < q`. It constructs a complete final word, its symbolic ambient
refinement, retention of all initial roots, preservation of the entire
initial word, a nonempty evaluated span, and Q preimages for every
source-relative target. The companion
`exists_complete_set_Q_transfer_of_source_refinement` constructs the fibre
frame from the explicit original source refinement and ambient support.

## General target existence and the exact positive-height threshold

This is a corrected **Q transfer theorem conditional on the supplied
local mixed word**. It neither constructs a local Ramsey witness nor
assumes a passed-in `Good` condition as a substitute for that existence
problem. The new `ForwardQFinalTargetExistence` module proves that the
eligible starred target class is nonempty for **every** admissible source
and supplied local mixed word when `q≥2`.

The boundary module `ForwardQFinalTargetHeightBoundary` proves that both
the actual set-signature and the stronger literal target classes are
**empty at local height q=1**. The retained cut
has final intrinsic rank m, whereas every final-support rank is less
than m+1. It has no strict descendant in that support. A same-complete-
signature starred target would have the same cut as an interior vertex,
which is impossible. Thus an actual target at positive local height
requires q>1. Combined with the general existence construction, the bound
is exact: at positive local height the target class is nonempty **if and
only if `2≤q`**. Nonemptiness of the constant evaluated span remains a
separate conclusion. This is the expected excluded boundary of the intended
Lemma 27 application: the existing audit records the paper assumption
`m′ < M−1`, and the architecture notes identify `q = M−m′`. Thus the
intended parameters already require q≥2. This result does not expose a
new error in the paper or change the final height `M = m+q`.

The positive regression `ForwardQFinalTargetNonemptyAudit` constructs an
actual starred target at the first permitted local height. Its parameters
are `b=2`, `n=k=3`, `l=1`, `m=0`, `q=2`, alphabet `Bool`, and fallback
`false`. The complete ambient support contains all seven binary nodes of
lengths zero, one, and two. The source tree consists of the root and its
two children, while the source word has its sole variable only at the
root and `false` at every other position. Each actual frontier coordinate
has a genuine height-two local word whose variables occur at their own
roots. All three source tree vertices survive in the final support.
Reading the source symbol at each final root gives an explicit uniform
substitution from the actual final interpolation to the source word.
Taking the source itself as target makes complete-signature equality
reflexive, including its literal tree-list order. Both the literal and
the actual set-signature transfer produce a genuine starred enlarged
input in the local mixed span with
the same tree-and-word observation. Thus this is positive starred-target
nonemptiness, distinct from the general nonempty evaluated-span result.
It is one concrete instance; its identity local components contain no
fixed auxiliary constants, and its root cut has an empty strict prefix.

The general witness is obtained by assigning the fallback original letter
to every final root, taking the actual induced enlarged starred input,
and applying fibrewise Q. In fact, every assignment of original alphabet
letters to the final roots gives an eligible target when `q≥2`.

The proof has three independent parts:

1. `ForwardQFinalInducedSignature` proves that **every** genuine enlarged
   starred Q output has the complete finite-set signature of its source.
   Its interior is exactly the source interior. Every exceptional source
   boundary has a corresponding output terminal extending that boundary,
   and every exceptional output terminal arises this way. Boundary
   uniqueness gives the same first-boundary node set. The fibrewise
   symbol law gives equality of the full strict rooted partial word,
   including its domain.
2. `ForwardQFinalInducedRefinement` supplies a uniform symbolic
   substitution from the final word to the actual induced Q word. Early
   final roots use the original source substitution; late roots use the
   chosen original alphabet letter. This distinction preserves the old
   variables and handles additional retained ambient roots correctly.
   Fixed auxiliary constants use their actual visible-ancestor decoder;
   no auxiliary letter is silently replaced by a fallback.
3. `ForwardQFinalInducedSupport` proves whole-tree support containment.
   The Q base lies in the retained initial support. Every marked Q leaf
   projects the intrinsic-rank-zero root of its local component. The
   ambient frontier has rank `m` or `m+1`, and `q≥2` places either projected
   root below the final height budget `m+q`.

`sourceRelativeSetTarget_nonempty_iff_two_le` combines this construction
with the height-one obstruction. The stronger source-facing assembly is

```lean
ForwardQFinalTargetExistence.
  exists_complete_nonempty_set_Q_transfer_of_source_refinement
```

It derives the genuine fibre frame from the actual ambient support and
source substitution, constructs the complete final word, retains every
initial root and symbol, proves its evaluated span nonempty, exhibits an
eligible starred target, and covers every eligible target by a genuine
starred Q preimage in the supplied local mixed span. All earlier APIs keep
their theorem types.

## Exact remaining obligations

The printed reverse-lex starred domain has not been identified with the
corrected forward domain. The known naive-reindexing counterexample is
preserved in `ForwardQStarredOrderReindexObstruction`; the corrected
forward order is explicit in the transfer's types. The merged Track E
work supplies the corrected forward canonical selector and its
source-independent simple-to-smooth transport. The quantitative
Corollary 22 repair, construction of the required local Ramsey witness,
relative colour control preserving the residual Γ₁ record, and the
Lemma 28/Theorem 25 induction remain separate work.
In particular, allowing a singleton original alphabet in this symbolic
transfer does not validate the printed unary Ramsey theorem.

## Validation surface

The new public declarations are included in the source-facing transitive
axiom registry. The full `DualTree` umbrella exports the construction,
its unchanged evaluated-span corollaries, and the unary regression.
Required validation is the full Lean workflow, finite skew/Q
regressions, source-integrity and minimal-import audit, TeX encoding
check, and the allowed-axiom gate at the same PR commit.

The paper-level signature and relative-refinement contracts and the
strict height restriction are in
[Todorcevic–Tyros, Definition 26 and Lemma 27](https://arxiv.org/pdf/2207.14599v1).
