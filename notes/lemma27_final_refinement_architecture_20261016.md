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
