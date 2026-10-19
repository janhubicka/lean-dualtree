# Exact criterion for full reverse Q-span coverage of CURRENT corrected f'

We have proved (merged PR #381) a full-domain evaluated equality between
the legal fibrewise corrected Q(x_sigma) and the ambient complete-skew f',
but only for assignments sigma ANCHORED on retained early roots to the
source substitution rho.

PR #384 proves any extra retained ambient root u not in the old source
variable support obstructs unrestricted reverse coverage over a two-letter
alphabet (rho(u) is constant or an old variable fixed at its own root).

Conversely, assume EVERY retained original T root is already an old source
g' variable root. Then any arbitrary final assignment sigma restricts to
the old source assignment tau(v) = sigma(ambient-old-root(v)). Since rho
fixes old roots at their own positions, anchoring sigma with this tau
changes NOTHING, while keeping new projected roots independent.
The whole-domain Q equality now covers EVERY final f' evaluation by an
ACTUAL corrected starred mixed-product point constructed from intrinsic
rank-zero local support roots.

Thus for positive branching b and q and a two-letter alphabet the exact
coverage criterion for the current corrected construction is:

  span(f') ⊆ union_(all enlarged w) span(Q_fibre(w))
       IFF
  retained(T,t0) ⊆ support(g').

The RHS also suffices using actual legal starred inputs, not only arbitrary
enlarged inputs. The LHS is interpreted as evaluated tree-word coverage,
not equality of variable WORDS with incompatible root-name types.

The separate numerical obstruction PR #385 shows that l<=m forces an
extra retained root and hence makes this coverage impossible in that
parameter regime. A future repair therefore needs either:
  (a) a complete-support embedding with no extra retained early roots,
      which must be checked against its full-branching requirements; or
  (b) a modified final-variable support/refinement and a new complete-skew
      argument; or
  (c) a different Ramsey pullback that does not require unrestricted
      evaluated reverse coverage.

The printed reverse-starred W_* and Definition 24 marker/simple
colouring transfer remain independent mathematical tasks.

## Numerical obstruction now included in the formal coverage criterion

Merged PR #385 formally proves that l<=m forces an extra retained T-root
outside the old g' source support. The present criterion therefore
immediately yields `not_hasReverseQCoverage_of_l_le_cut_rank` for positive
b,q and a two-letter alphabet. The reverse direction remains conditional
on no extra retained roots; this need not hold for the original embedding.
