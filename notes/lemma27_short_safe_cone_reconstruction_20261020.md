# Safe-cone reconstruction and the actual shortened sampler

An important distinction survives the earlier correction of
Lemma 27: `selectedFrontier c t = some i` does not imply the
canonical inverse local tail of t lies inside the shortened local
word domain of length `k-(m+1)`.

This follow-up uses the verified inverse-prefix theorem to write
the inverse address of every T-node above frontier_i as

    inverseAddress(t) = inverseAddress(frontier_i) ++ tail.

Whenever `tail` fits the shortened domain, the already verified
`projectLocal_inverse` and complete-support bijection identify t
with P_i(tail). Hence its actual `safeAddress` is `some (i,tail)`.

The contrapositive implies that at a node with `safeAddress=none`
the enlarged Q sampler uses the original fallback constant, even
when a frontier index exists. The theorem uses the actual
`sampledEnlarged` definition rather than an abstract patched word.

Next: combine this with the selected-frontier/no-frontier cases of
the actual fibrewise Q and the verified forced output fallback in
PR #400 to discharge the last unsafe late-root symbol comparison.
This will prove all *word symbols* match, still not exact equality
of starred Q trees or local mixed-product Ramsey-span membership.
