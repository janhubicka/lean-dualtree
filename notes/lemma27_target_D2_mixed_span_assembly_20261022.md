# Assemble exact target D2 points into a mixed-product span witness

For each original source marker r, the previous formalization
chooses the unique target terminal and its true local tail z_r,
with P_(bulletForMarker(r))(z_r) equal to that target terminal
and z_r in the relevant f_i variable-root support.

The original source R↔BulletIndex equivalence now fills EVERY D2
slot with that marker's exact point. We retain the ordinary
component words from the previously verified inducedPoint,
whose evaluations already belong to the local mixed Ramsey span.

The resulting targetMixedPoint is a genuine member of f.span
and all its marked D2 projections are the exact target terminal
nodes of O. Unlike the earlier induced point, its D2 positions
are selected specifically to match O and need not be rank-zero.

The remaining global starred constraint is precisely:
BulletLengthsOrdered c targetMixedPoint
(or equivalently the corrected singleton-vector IsStarred).
It is NOT established merely from individual local support
membership. We keep an explicit theorem deriving IsStarred
from that condition, rather than silently assuming it.

Next: use the target-marker/target-leaf bijection and the same
signature interior theorem to prove equality of Q tree vertex
SETS with O.tree; then investigate whether target O's
semi-completeness implies the corrected global order of the
selected local D2 points, or whether additional hypotheses
are needed. Exact starred-object surjectivity is not yet
validated.
