# Adversarial audit of the dual-tree Lean library
15 October 2026 — ongoing audit ledger; read together with \`audit.tex\`

## Scope and evidence policy

This is a **proof-engineering and paper-alignment audit**, not a claim that
Todorcevic–Tyros' entire dual-tree theorem has been verified. The exact
Lean toolchain and two source libraries are pinned in \`lakefile.toml\`.
The successful main-branch CI at the beginning of this pass audited
**1,326 selected source-facing declarations** using transitive
\`#print axioms\`, allowing only \`propext\`, \`Classical.choice\`, and
\`Quot.sound\`. A green check proves that the registered Lean declarations
compile with those axioms. It does **not** prove that the registered list
covers every theorem, that definitions match all published ones, or that
the unpublished corrected forward-order hypothesis follows from the
published starred mixed-product hypothesis.

Three distinct adversarial passes are tracked:

### 1. Mathematical statement and hypothesis audit

| Item | Verified scope | Obstruction / remaining adversarial challenge |
|---|---|---|
| The printed Q leaf-replacement and reverse-lex auxiliary order | Kernel-checked finite counterexample and typed starred-domain checks in the QLength/SkewOrder modules | The **construction/proof** fails as printed; do not infer that the final existence theorem is disproved |
| Corrected forward Q support and star domain | Forward source/frame construction, exact interiors and leaves, closure, canonical D2 ordering; semicomplete support when selected bullet lengths satisfy order-reflecting vector-one certificate | No general translation of the printed reverse-lex W_* starred family to the corrected forward family; naïve reordering is independently disproved |
| Source canonical addresses and model A | Complete first-l interior and A_l ≃ source leaves ≃ literal R ≃ D2; model-labelled Q vertices, prefix/direction/rank invariants | The published Definition 24 canonical map I_U on arbitrary semi-complete starred U still needs an explicit definition and identification, **including l=0** |
| Colouring pullback | Corrected R-relative, then source-relative A-indexed simple colourings pull back to smooth colourings and have total smooth extensions | A general colouring simple for the **paper's I_U** has not been shown to satisfy the source-relative hypothesis; the input domain may differ |
| Full-frontier Q words | Generic decoders, exact evaluations, fibrewise ambient substitution and conditional Hall matched tagged-variable span in forward Q modules | The paper-specific variable names, full span of its raw cone words, simultaneous visible-root Hall capacity, and ordering of W_* must be supplied before Ramsey application |
| Ramsey induction | Generic product, partite and smoothness interfaces, partial Lemma 27 ingredients | Lemmas 27–28, Theorem 25, recursion inequalities, and final Theorem 3 have **not** been established |

**Do not weaken a failed condition by replacing it with an assumed
certificate without declaring the changed theorem.** For every theorem
used downstream, record whether its hypotheses are original,
corrected, or intentionally conditional.

### 2. Lean trust and transitive-dependency audit

- \`scripts/CheckDualTree.lean\` is an explicit curated set of axiom endpoints.
  \`scripts/check-axiom-log.py\` rejects \`sorryAx\`, other unexpected
  axioms and a mismatching endpoint count.
- Add \`scripts/audit-lean-library.py\` to report **every source module's**
  static import closure, redundant umbrella imports, unimported files,
  and lexical candidate declarations (\`sorry\`, \`admit\`, \`axiom\`,
  \`opaque\`, \`unsafe\`, \`native_decide\`). A private declaration that
  appears only once is a **candidate** for review, not automatically dead.
- \`lake build\` establishes type checking; the separate finite Python
  regressions test only bounded examples. They are not a proof of
  correctness for arbitrary parameters.
- Transitive \`#print axioms\` endpoint count is **not a completion
  percentage**. Every new theorem and any exported high-value witness
  should be registered explicitly.

### 3. Maintainability / API / obsolete code audit

- \`DualTree.lean\` imports a historical succession of nearly every
  module, with many direct imports already guaranteed transitively.
  The audit script computes a *minimal root import cover*, while
  retaining the full transitive closure of currently exported modules.
  This is the first safe cleanup: remove redundant imports, **not**
  entire proof files merely because another module imports them.
- The older \`QLength*\`, \`SkewOrderObstruction\`, and \`QOrderRepairAudit\`
  branches are **counterexample/regression evidence** and must not be
  erased as "dead ends" without an explicit replacement for their
  kernel-checked counterexamples.
- Clearly separate real output from obsolete placeholder constructors.
  For example, \`ForwardQActualStarredSpace.placeholderStarredWordOnQ\`
  explicitly states it is only a typed *placeholder*, not Lemma 27's
  actual g_w. It may be removable *after* proving no imports or
  explicit axiom-audit endpoints rely on it; deleting it before that
  check would silently change verification coverage.
- Many historical README milestones still say "CI pending" even
  after later successful merges. Treat these as archival history.
  Maintain a concise current status above them and use the
  mathematical TODOs in \`audit.tex\` as a cumulative ledger.
- Do not add compatibility wrappers for internal module APIs unless
  actual downstream consumers require them. Check three closely
  related repositories before changing the pinned Todorcevic
  Ramsey-space and successor-tree dependencies.

## Next formalization / review gate

1. Finish and CI-check the full corrected model-to-Q **prefix** relation
   in PR #302; then verify every **first outgoing direction** so the
   source-address walk defines exactly the canonical Q map.
2. Define the unique canonical map on arbitrary relevant
   semi-complete starred U (including the zero-interior convention).
   Prove its values agree with the relative A-selector on all source
   refinements where simple colourings are applied, or identify the
   precise additional hypothesis / counterexample.
3. Reconcile the printed W_* domain and actual corrected forward D2
   domain; avoid naive reverse-to-forward order reindexing.
4. Discharge concrete source-cone word, Hall/capacity and global span
   obligations, then the mixed-product refinement and Lemma 28
   iteration. Only then attempt Theorem 25 and Theorem 3.

The script is a *machine-executable static audit* and its output is
intended to be incorporated into future cleanup commits. A declaration
must remain until its absence is checked against both Lean imports and
the source-facing theorem audit. 


## Static inventory from the first green source audit

The scanner on the pre-cleanup umbrella found **262 local Lean modules**
(including \`DualTree.lean\` itself); **261** source modules were reachable,
and **none** was unreachable. The historical root contained **260**
direct imports, of which **239** were already guaranteed by its other
direct imports. After merging the next source-facing prefix-isomorphism
module (#302), the root import cover requires only **21** essential
imports and retains the *same* 262-module transitive closure.

There were no uncommented local \`sorry\`, \`admit\`, \`axiom\`,
\`opaque\`, \`unsafe\` or \`native_decide\` tokens, and zero private
declarations with the crude one-occurrence unused signature.
These are useful negative findings, **not** proof that all public
declarations are actively needed or that all semantic lemmas match the
paper. This cleanup removes root-import duplication without deleting
counterexample fixtures or source-facing theorem implementations.
The independent static CI now rejects a redundant umbrella import,
so duplication cannot silently reappear.
