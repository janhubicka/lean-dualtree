# Correct D2 frontier index for each supported target terminal

We previously validated that:
- the original source and requested target share the literal R marker
  nodes under equal COMPLETE forward signatures;
- every supported target terminal extends an original source R marker;
- each such target terminal has an actual shortened safe address.

The missing link is now proved with full original T geometry.

For a literal R marker r and T vertex t extending r, the chosen
source frontier f_r also prefixes t. Both f_r and t lie in the
meet-closed complete support. Their longest common prefix is in T,
lies above r, and hence lies outside the inclusive cut. Minimality
of the frontier forces this meet to equal f_r.

If t is represented by safeAddress(t)=some(i,z), its own frontier_i
also prefixes t. Two minimal outside-cut T frontiers below the same
vertex must coincide, and the sorted frontier map is injective.
Thus i is exactly the original D2 index bulletForMarker(r).

Consequently every terminal t of a target O with the same complete
corrected signature and O.tree ⊆ the exact final support T'_M has
a safe address (bulletForMarker(r),z) for a source literal marker r.

Still open: prove the chosen local tail z lies in the coordinate
variable support of f_i, establish corrected D2 vector-one order
for all such target tails simultaneously, assemble the corresponding
mixed point, and finally prove its Q-tree equals O.tree. The existing
full word-preimage proof is separate and already verified.
