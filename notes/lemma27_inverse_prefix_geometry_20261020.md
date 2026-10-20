# Prefix reflection in the actual complete-support coordinates

To settle the Q sampler at late unsafe ambient f roots, one must not
conflate `safeAddress = none` with `selectedFrontier = none`.
The latter selector can exist even when the canonical local tail
is too long for the shortened mixed coordinate domain.

This module establishes the missing generic geometry:

1. A genuinely admissible support walk remains admissible after
   concatenating a path from its actual endpoint.
2. The finite canonical inverse `inverseAddress` of a complete
   forward-skew support maps support prefixes to source-word prefixes.

The second proof combines the previously verified
`walk_address_of_prefix_forward` with exact uniqueness of
admissible walks; it does not postulate a tree-order inverse.

Next: if an actual complete-support vertex t lies above frontier i,
its inverse address has the form inverse(frontier_i) ++ tail.
If tail belongs to the shortened local domain, the existing
`projectLocal_inverse` and inverse bijection reconstruct t as
P_i(tail), contradicting `safeAddress t = none`.

This is a reusable prerequisite, not yet the Q fallback theorem.
