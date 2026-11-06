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
| Corollary 22, p. 25 | The height-one marked-letter colouring is smooth and has a c-good word, but is not monochromatic. The displayed threshold omits a resource needed to remove marked-letter dependence. The `d₂ = 0` call to positive-dimensional CT also needs a separate convention or case. | Separate the algebraic colour argument from Ramsey existence. `Corollary22TwoRootRepair` proves the two-root erasure mechanism on actual mixed spans. A revised `max{2, CT(...)}` intermediate dimension is still a proposed numerical wrapper until the CT/refinement/existence steps are assembled. |
| Lemma 27, pp. 28–29 | Enlarged alphabet, cone domains, decoded variables, Q ordering, fixed-signature coverage, and the final refined word all need the recorded repairs. Evaluated-word coverage alone is insufficient for a colour of starred objects. | One-signature canonization must yield an actual syntactic refinement, retain the prescribed initial roots, and colour the complete semantic signature fibre. The local step is an explicit input to `Lemma28.LocalFusionStep`; no unproved step is installed as an axiom. |
| Lemma 28, pp. 29–30 | The iteration suppresses transport of model signatures into the changing current word. Plain refinement preserves a fixed ambient fibre, but need not preserve the interpretation of a model signature. | `finite_signature_fusion` proves the iteration from one-signature canonization plus preservation of earlier model interpretations. `finite_signature_canonization` additionally requires final signature coverage. The number of tasks must be computed in the finite model tree independently of the ambient height. |
| Theorem 25, pp. 27, 30–31 | The pullback must be simple. Its induction is used inside a prescribed source word although the printed theorem is global. The displayed comparison of PTGR with TGR is false; PTGR also suppresses the alphabet parameter. | `CorrectedTheorem25` and `PTGRBound` retain alphabet size and an explicit selector. The transfer module requires relative Ramsey input and refinement-local coverage. No numerical TGR/PTGR comparison is imported. The complete node count is a finite power sum, valid also for branching one. |
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

1. Tracks A–C: supply the full mixed Ramsey existence and higher-height
   complete-skew refinements needed by the local canonization step.
2. Track D: supply corrected Q/refinement construction and exact semantic
   fixed-signature coverage for the required local witnesses.
3. Track E: supply canonical selector transport, the required smoothness
   and simplicity bridges, and preservation of the residual point data.
4. Track F: instantiate the finite model signature enumeration, its
   increasing-cut transport laws, and final coverage; derive the relative
   induction interface from the canonical model embedding; discharge the
   `l = 0` base case and assemble the actual induction over `l`.
5. Prove the corrected qualitative main theorem and its conversion to the
   non-unary span version; then prove the numerical wrappers, comparison
   statements actually used, and the independent product theorem.

The full corrected Lemma 28, Theorem 25, and Theorem 3 therefore remain
open. This change proves reusable parts of their assembly and the local
two-root colour argument, with the mathematical inputs explicitly exposed.

## Validation

New source modules are registered in the full `DualTree` import umbrella.
Their public proof endpoints are registered in `scripts/CheckDualTree.lean`.
This change adds 32 endpoints; after integrating #522–525 and #529, the
registered total is 2,229. This count is not a percentage of the source theorem.
Lean compilation, the existing source/axiom gates, and finite Q regressions
are required before the change is reported as verified. See the pull
request's checks for the tested commit; this note makes no claim about
unrun tests or completion of the target propositions.
