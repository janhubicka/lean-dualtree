# Conditional reverse-span obstruction in corrected Lemma 27

This is an intentionally adversarial source-facing claim, not a
counterexample to the main Ramsey theorem.

Suppose the original f has two DISTINCT retained variables u,v at
or before the forward auxiliary cut and the source refinement
g'=f[rho] sends them to the SAME old source symbol:
  rho(u)=rho(v).

For every enlarged mixed-product input w (even BEFORE enforcing
the starred W_* domain), genuine fibrewise Q(w) has the same
symbol rho(u)=rho(v) at the two original f-root positions.
Therefore EVERY evaluation under an old source assignment tau
has equal values at those two positions.

By contrast the corrected final support T' retains u and v
as distinct independent f'-variables, with exact root symbols.
Over any alphabet alpha with two distinct letters a≠b, assign
a to u and b to v in f'. This produces a genuine element
psi of span(f') whose values at u and v differ. It is NOT
an evaluation of ANY Q(w), for any w and tau.

Formal consequence:
  span(f') is NOT in general a subset of union_w span(Q(w)).
Our proven positive whole-domain result goes in the OTHER
direction: for every tau and base assignment sigma0, there
is a specially ANCHORED sigma with
  eval(Q(x_sigma),tau)=eval(f',sigma).

Thus a proposed unrestricted
  [S,f'] ⊆ Q(span(f_i))
must either be a statement about a RESTRICTED set of starred
refinements that enforces g' early compatibility, or the
construction of f' (in particular its early support/word
semantics) must change. Mere complete skewness and root-wise
span inclusion do not solve this obstacle.

The conditional theorem does NOT assert that every legal
source Frame has a collapsed pair rho(u)=rho(v); a concrete
instantiation must be checked separately. It also does not
refute the conclusion of Lemma 27 or the main theorem.
The printed reverse-starred W_* mismatch remains independent.
