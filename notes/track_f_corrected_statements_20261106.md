# Track F: corrected statements and conditional induction

Scope: [issue #519](https://github.com/janhubicka/lean-dualtree/issues/519),
branch `track-f/theorem-induction`. Starting commit:
`910efe61e94a284be065f4a782bec878c5d1170f` (merged #513).
During the pass, main advanced through #522–525 and #529 to
`4306242fc876b0ddc03143caea8a3abc433568d9`.
That integration is included, retaining the new interleaved height-one
Track A results and all twelve of their audit endpoints. These include
exact nonempty spans and unique factorization through the full observed
D₂ marker tuple; they do not yet provide D₁ or higher-height existence.
The continuation also integrates Track E from main
`cce5b81bc17ed4b9140d06eebc705a45d9bc41ae` and consumes the verified
Track D source at `6237c4a1ce3b26e483b7399770ae3d42d90bf4bd` from #527.
Track E supplies the intrinsic selector and total smooth Q extension;
Track D supplies the actual complete refinement and set-signature Q
preimages. The new F results compose those proved inputs.
This continues the A–G split in the **T A** chat. Tracks A–E supply
mathematical construction and transport inputs; this track owns their
statement-level integration and the final induction. It does not close
those other tracks by assuming their conclusions without identifying them.

Source: Todorcevic–Tyros,
[arXiv:2207.14599v1](https://arxiv.org/html/2207.14599v1),
especially §§1.3, 4, and 5. The existing `audit.tex` records the checked
counterexamples. This note changes neither the original paper nor its
historical validation markers.

## Conventions fixed for this track

1. **Forward auxiliary order.** Complete and semi-complete supports use
   `SkewTree.forwardAuxB`. The printed reverse-order construction remains a
   separately audited, failing construction. No equivalence with that
   construction is inferred from the present work.
2. **Syntactic refinement.** A refinement is a single uniform substitution
   of all original variables. For alphabets with two distinct letters this
   is equivalent to evaluated-span inclusion. The syntactic target also
   includes one-letter alphabets, where span inclusion is insufficient.
3. **Semantic colour domains.** Ordinary words are observed by their full
   root-labelled function. Starred words are observed by the finite vertex
   set and that function. Permuting a support list is not a new mathematical
   object. Arbitrary colours of raw Lean records are therefore not the
   theorem's colour domain. The observation type agrees with the existing
   corrected-Q observation API.
4. **Ambient and intrinsic heights are different parameters.** All
   refinements in a fusion retain the ambient homogeneous-tree height;
   their complete-support heights decrease along a separately supplied
   schedule. An eventual bound means a positive threshold working for
   **every** ambient height at least that threshold.
5. **Quantitative objects require existence.** `leastBound` requires a
   proof of an eventual-bound witness. No default value, new axiom, or
   opaque Ramsey-number definition hides an unproved existence theorem.
6. **The canonical selector is fixed.** `CanonicalTheoremSpec` uses the
   intrinsic boundary map on arbitrary semi-complete supports, including
   the singleton boundary at zero interior. The original selector-parametric
   interface remains available for reuse; the concrete target has no free
   selector choice.

The numerical target predicates use the canonical alphabet `Fin ell` and
colour set `Fin r`. Their transport to arbitrary finite alphabets and colour
sets of the stated sizes remains an explicit source-comparison obligation.
The conditional fusion and colour-transfer results themselves are already
polymorphic in both types.

## Printed versus corrected statement ledger

| Source | Issue in the printed statement or proof | Target and current boundary |
| --- | --- | --- |
| Theorem 3, p. 3 | Unary evaluated spans collapse. The checked obstruction holds at every sufficiently large ambient height. Raw support-list colours would create an additional representation error. | `CorrectedTheorem3`: all positive branching, alphabet, source/target dimensions and colour counts; positive eventual threshold; syntactic refinements; semantic colours. The equivalence with the span conclusion is proved under `HasTwoLetters`. The Ramsey existence claim remains a target proposition. |
| Theorem 13 / Definition 12, p. 11 | Mixed-product construction still needs genuine D₁ leaves, higher intrinsic heights, and relative use inside prescribed source words. Corrected ordered geometry must be used consistently. | Actual `MixedProduct.VariableWord` and `Good`, with an explicit finite coordinate-kind map and complete-skew support. Main now includes arbitrary D₀/D₂ interleavings at height one; these are not promoted to the full theorem. Existence beyond that scope is not supplied by this track. |
| Corollary 22, p. 25 | The height-one marked-letter colouring is smooth and has a c-good word, but is not monochromatic. The displayed threshold omits a resource needed to remove marked-letter dependence. The `d₂ = 0` call to positive-dimensional CT also needs a separate convention or case. | `Corollary22TwoRootRepair` proves two-root erasure on actual mixed spans. `Corollary22CanonicalQ` now applies it to the total smooth extension of an actual canonical-simple Q colour. Only selected canonical boundary points remain; when the selected set is empty, the starred Q image is monochromatic without a CT selection. A revised `max{2, CT(...)}` bound remains unproved until Ramsey existence and the nonempty residual-point case are assembled. |
| Lemma 27, pp. 28–29 | Enlarged alphabet, cone domains, decoded variables, Q ordering, fixed-signature coverage, and the final refined word need the recorded repairs. Evaluated-word coverage alone is insufficient for a colour of starred objects. | `Lemma27CanonicalColor` proves the empty-selected-boundary case from a supplied full-span c-good local word of dimension at least two. It constructs the actual complete syntactic refinement, retains every initial root and rooted symbol, and proves `Lemma28.FibreMonochromatic` for the entire fixed set-signature fibre. Q coverage is proved by Track D, not assumed. Local mixed Ramsey existence and the general boundary partition remain open. |
| Lemma 28, pp. 29–30 | The iteration suppresses transport of model signatures into the changing current word. Plain refinement preserves a fixed ambient fibre, but need not preserve the interpretation of a model signature. | `finite_signature_fusion` and `finite_signature_canonization` prove the conditional iteration. `Lemma27CanonicalColor.canonicalSignature` now supplies a genuine signature function, with a uniquely determined forward-maximal interior cut, and identifies its eligible fibres exactly with Track D's target class. Increasing-cut model transport, final coverage, and an ambient-independent model task count remain open. |
| Theorem 25, pp. 27, 30–31 | The pullback must be simple. Its induction is used inside a prescribed source word although the printed theorem is global. The displayed comparison of PTGR with TGR is false; PTGR also suppresses the alphabet parameter. | `CanonicalTheoremSpec.CorrectedTheorem25` fixes the audited intrinsic selector and retains alphabet size and all nonnegative interior counts. The transfer still requires relative Ramsey input and induced-colour simplicity. No numerical TGR/PTGR comparison is imported. The complete node count is a finite power sum, valid also for branching one. |
| Theorem 29, p. 32 | The product extension has no independent proof in the paper and also inherits the unary span-refinement problem. Scalar homogeneity does not automatically supply simultaneous product homogeneity. | `ProductRamseyAt` uses genuine vector-complete supports, including cross-coordinate order and level separation, semantic colours, and componentwise syntactic refinements. Product existence, source comparison, and quantitative bounds remain unproved. |

The positive-alphabet hypotheses above are deliberate. The Lemma-27 source
uses an alphabet of size at most the supplied bound and chooses a fallback
letter, so the nonempty-alphabet condition must be retained when that local
statement is instantiated. Its other parameters include a positive `l`,
an intrinsic cut level `m'`, and `m' < m - 1`. None of those requirements is
discharged merely by the general fusion theorem.

## What the formal modules establish

### CorrectedTheoremSpec

`StarredBelow` checks both containment of the **whole starred tree** in the
enclosing complete support and a uniform substitution of the whole ambient
word. `starredBelow_of_syntacticRefines` proves that both clauses survive
further refinement. This is the eligibility fact needed repeatedly by the
induction.

`TreeRamseyAt`, `StarredRamseyAt`, `TGRBound`, `PTGRBound`,
`CorrectedTheorem3`, and `CorrectedTheorem25` are named target propositions.
Their presence is not evidence of existence. `SimpleWith` compares genuine
rooted symbols and exposes the Definition-24 selector and its boundary
subset. Track E must supply the canonical selector, including the `l = 0`
root convention, before the partial-tree target is instantiated.

The proven conversion `wordMonochromatic_iff_span` gives the ordinary
span-based conclusion for nondegenerate alphabets. The analogous starred
relation is handled by `starredBelow_iff_span`. `completeNodeCount` replaces
the expression dividing by `b - 1`; its branching-one value is proved to
be the intrinsic height.

`MixedRamseyAt` puts c-goodness in the conclusion of the actual
mixed-product existence target. `ProductRamseyAt` keeps the complete
cross-coordinate geometry of the source product theorem. Neither target
is declared proved by this interface.

### Lemma28

Fix actual ambient starred objects, a signature map `sg`, a colour `c`, a
finite model-task count `P`, and a current-word-dependent interpretation
`transport f i` of task `i`. A step from `f` to `g` must provide:

- the actual syntactic refinement `g ≤ f`;
- homogeneity of the new signature fibre at `transport g p`;
- equality `transport g i = transport f i` for every earlier `i < p`.

Finite induction composes the substitutions and preserves all earlier
homogeneous fibres. Final coverage says that every eligible starred object
has signature `transport g i` for some `i < P`. These two statements give
signature canonization for all actual starred refinements of the final word.

An arbitrary stage-height function is allowed. The included uniform-budget
helper consumes exactly one application of a supplied one-step bound per
task and ends at the prescribed height. It does not certify that the supplied
bound is a valid Ramsey bound. The sharper source schedule, depending on the
successive cut depths, can be supplied through the same stage-height API.

An empty fibre is treated by pairwise equality and needs no chosen colour.
An empty task list does not make coverage true: coverage would then require
that the final eligible domain were empty. This avoids a vacuous shortcut.

### Corollary22TwoRootRepair

For a Γ₁ coordinate with a second support root, first move the marker to
that other root while keeping the entire word fixed. Smoothness preserves
the colour. Reset the variable at the original marked root; c-goodness
preserves the colour because the temporarily marked root retains its value.
Move the marker back and use smoothness again. All intermediate points are
proved to lie in the original mixed span.

Those marker moves need not preserve the extra starred ordering. This is
why the proof uses c-goodness on the **full mixed span** and **global**
smoothness. Smoothness known only on the starred subset is insufficient;
an application must provide the separately verified total smooth extension.

Combined with the existing Γ₂ marked-letter erasure, colours depend only on
the Γ₂ marked **points**. In the all-Γ₁ case the whole mixed span is
monochromatic, conditional on the supplied c-good word and smoothness.
No assertion is made that the underlying marked-letter records are constant;
the existing record-variability obstruction remains valid.

The resource is also obtained from actual complete-support dimension:
`complete_support_has_two_roots` proves that intrinsic dimension at least
two forces two distinct variable roots. Thus
`good_smooth_color_eq_of_two_le_dimension` requires only `k ≥ 2`, the
supplied c-good word, global smoothness, and equality of the Γ₂ points.
It still does not provide the mixed Ramsey word or the CT refinement.

### CanonicalTheoremSpec and Corollary22CanonicalQ

The actual canonical boundary map now instantiates the theorem target.
Global semantic simplicity implies Track E's source-relative simplicity
over every alphabet. Source-relative evaluated-span simplicity restricts
to syntactic refinements without an alphabet hypothesis. The reverse
relative bridge is proved only with `HasTwoLetters`; no unary equivalence
of those different refinement domains is asserted.

Track E chooses a total globally smooth extension of the Q pullback before
the local mixed word is supplied. On a c-good word of intrinsic dimension
at least two, the two-root argument removes all marked-letter dependence.
Injectivity of the genuine cone projection identifies equality of local
Gamma2 points with equality of the selected canonical boundary points of
the Q outputs. Thus the selected boundary points are the only residual
colour data.

When `B2` is empty, the actual starred Q image is monochromatic. This does
not require the D2 coordinate type to be empty: every D2 coordinate then
belongs to Gamma1. Goodness is required on the whole span over the enlarged
alphabet, for the same total colour selected before the word. Goodness
only on the starred subset or only over the original alphabet is insufficient.

### Lemma27CanonicalColor

The positive-interior signature is now a function, not a relation with a
free cut parameter. A finite-order maximum supplies the last interior
vertex, and antisymmetry proves its uniqueness. The signature retains the
finite signature-node set and the entire optional rooted partial word,
including its strict domain. It is exactly Track D's complete set signature.

The main local theorem `exists_total_emptyBoundary_fibre_canonization`
starts from a globally canonical-simple semantic colour with empty `B2`.
It chooses one total smooth enlarged-Q colour. Every c-good local word for
that colour with intrinsic dimension `q ≥ 2` then gives an actual
`(m+q)`-complete final word with:

- a uniform syntactic refinement of the supplied ambient word;
- retention of every ambient variable root through the inclusive forward cut;
- preservation of every initial constant and rooted variable symbol;
- a nonempty evaluated span;
- monochromaticity of the entire eligible fibre of the source's canonical signature.

The last conclusion uses the proved exact equivalence between that fibre
and Track D's source-relative set-signature target class, followed by its
actual Q preimages. No target-coverage or target-monochromaticity hypothesis
is supplied by the caller. The theorem uses no two-letter assumption.

This is the empty-`B2` local step at positive interior count, **not** the
`l = 0` induction base. Nonemptiness of the final evaluated span also does
not assert that this particular signature fibre is inhabited. General
fixed-target existence remains separate. The supplied c-good word is still
the substantial mixed Ramsey input; its existence has not been proved here.

### Theorem25

Signature canonization is used to define a colour on realized signatures,
with an explicit default colour for unrealized signatures. The transfer to
the lower-interior-count starred domain needs coverage **inside every
further refinement**; global surjectivity of a map is not a replacement.

The final induction interface distinguishes:

- the canonical-signature result obtained from Lemma 28;
- construction and simplicity of the lower colour;
- relative Ramsey existence below the prescribed current source word;
- hereditary signature coverage and colour compatibility.

The module proves the transfer after these inputs are supplied. It does not
claim that defining a pullback proves it simple, or that a global induction
hypothesis is automatically valid relatively.

## Remaining integration work

1. Tracks A–C: extend the proved nonvacuous no-D1 height-one construction
   to D1, higher intrinsic heights, eventual ambient-height bounds, and
   the relative refinements required by local canonization. The new local
   theorem specifically needs full-span c-goodness over the enlarged alphabet.
2. Use the completed Track D Q/refinement coverage and Track E canonical
   smooth extension throughout the local construction. Establish residual
   point homogenization for nonempty `B2`, with the required refinement
   and quantitative control; general fixed-target inhabitation remains separate.
3. Prove simplicity of the actual lower-interior colour and the relative
   Ramsey input needed by Theorem 25. The initial canonical Q smoothness
   theorem does not by itself prove this later induction hypothesis.
4. Track F: instantiate the finite model signature enumeration, its
   increasing-cut transport laws, and final coverage; derive the relative
   induction interface from the canonical model embedding; discharge the
   `l = 0` base case and assemble the actual induction over `l`.
5. Prove the corrected qualitative main theorem and its conversion to the
   non-unary span version; then prove the numerical wrappers, comparison
   statements actually used, and the independent product theorem.

The full corrected Lemma 28, Theorem 25, and Theorem 3 therefore remain
open. The empty-selected-boundary local colour step now has an actual
complete refinement and the full fixed-signature conclusion; the general
local Ramsey and model-transport inputs remain explicitly exposed.

## Validation

New source modules are registered in the full `DualTree` import umbrella.
Their public proof endpoints are registered in `scripts/CheckDualTree.lean`.
Track F now adds 52 proof endpoints, including 20 in this continuation.
With the integrated Track D and E results, the registered total is 2,421.
This count is not a percentage of the source theorem.
Lean compilation, the existing source/axiom gates, and finite Q regressions
are required before the change is reported as verified. See the pull
request's checks for the tested commit; this note makes no claim about
unrun tests or completion of the target propositions.
