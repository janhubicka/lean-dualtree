# Revisit Definition 26: fixed-signature versus full evaluated span

The manuscript's Definition 26, arXiv:2207.14599v1 p.27,
defines [S,f] as the set of STARRED l-variable-word refinements
of f whose signature sg is equal to the fixed S=(S',g').
It is NOT the entire evaluated span [f]_Lambda of constant words.

Consequently the new verified no-extra-retained-root criterion
(PR #386) and numerical noncoverage theorem (PR #385) diagnose
unrestricted CONSTANT evaluation span coverage of the constructed
forward-corrected f', but do not prove or refute the actual
Lemma 27 inclusion:
  [S,f'] ⊆ { Q(w) : w in the mixed starred Ramsey subspace }.

The correct intermediate predicate is EARLY COMPATIBILITY of an
evaluated word psi: there exists one assignment tau to the old
source roots such that at ALL original f-variable roots u before
cut, psi(u)=evalSymbol(tau,rho(u)). The existing construction of
f' fixes each old retained original f root at its own location.
Therefore for psi in span(f'), early compatibility is equivalent
to psi having an actual corrected starred Q evaluation witness.

We prove that equality on ALL ambient positions, not just roots:
- An arbitrary corrected Q evaluation is early-compatible.
- An arbitrary early-compatible psi in span(f') determines an
  assignment sigma to final roots which is ALREADY equal to its
  tau-anchoring, so the verified whole-domain Q equality supplies
  a corrected W_* input from the genuine mixed-word span.
- A general refinement h of f' with an early-compatible evaluated
  span inherits the Q coverage of all its constant evaluations.

These results do not automatically establish the actual
VARIABLE-WORD-level inclusion in Lemma 27: a starred word h
with sg(h)=S needs a precise encoding and proof that its
restricted signature forces early evaluation compatibility.
Moreover the Q witness must match the whole starred word and
tree component, not merely its constant evaluations.
Definition 24 simplicity and the paper's reverse-order Q remain
separate obligations.

Do NOT describe the numerical obstruction to full span(f')
coverage as a counterexample to Lemma 27 itself. The two sets
differ in type and in quantified early-root constraints.
