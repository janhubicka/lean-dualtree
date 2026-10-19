# From Definition 26 rooted prefix symbols to compatible Q evaluations

Definition 26 fixes the signature's restricted VARIABLE WORD g', not
an arbitrary common evaluation of final f'. To avoid confusing
dependent variable-name subtypes, compare rooted symbols via
CutPreservation.underlyingSymbol : Sum α (BoundedNode b n).

For an actual variable-word refinement h, the sufficient
source-signature conditions are:
 (i) every old source g' variable root also belongs to h.support;
(ii) at every original ambient f-variable root u at/before the
     forward cut, the underlying symbol of h equals that of g'.

The two conditions give a canonical old-variable assignment
tau(v) = eta(the identical root v inside h.support) for every
evaluation eta of h. Equality of underlying rooted symbols implies
equality of the evaluated letters even though the dependent
Var types differ. Since g'=f[rho], this proves the resulting
constant word ψ=eval(h,eta) is EarlyCompatibleValue(g,ψ).

The already verified restricted reverse-coverage theorem then
supplies a GENUINE corrected starred Q input for every ψ∈span(h),
provided h.span⊆span(f'). No extra-retained-root assumption.
This explains why the conditional full-span obstruction is
compatible with the original paper's signature-restricted goal.

Still to formalize:
- actual (S,h) in the paper's fixed-signature fibre
  [S,f'] implies these two rooted-prefix conditions, including
  the source's precise D/s≤t0 boundary convention;
- upgrade equality of CONSTANT evaluations to equality of the
  l-variable-word STARRED Q output object with (S,h), preserving
  its skeleton and variable names;
- Definition 24 simple-colouring pullback, original reversed
  auxiliary-order W_* alignment, and the Ramsey recursion.

The current theorem does not claim the paper's Lemma 27 completed.
