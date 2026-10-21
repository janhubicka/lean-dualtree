# Exact target Q vertex SET equality after D2 selection

The selected local D2 points for each source R marker have already
been shown to belong to the correct component variable supports.
The assembled targetMixedPoint is therefore in the real local
mixed-product span, with all selected D2 projections equal to
the corresponding TARGET O terminals.

This patch verifies set-level equality of the complete corrected Q
support and O.tree:
  nodes(c,targetMixedPoint) = O.tree.toFinset.

Forward inclusion: old Q base equals the source interior, which
equals the target interior by identical literal signatures; every
marked projection is a selected target leaf.
Reverse inclusion: old target interior belongs to the Q old base;
each target leaf has a target R marker, transported to an original
R marker by the exact signature-node correspondence; its unique
selected target leaf is that same leaf, so the corresponding Q D2
projection covers it.

This equality is intentionally about FINITE NODE SETS. The order
of the arbitrary list representations is not assumed equal.

Major remaining global step: prove the EXACT selected D2 local
point tuple satisfies the corrected forward W_* vector-one/order
predicate. Even complete Q support set equality and full coherent
word decoding do not establish this. Under that global condition,
the already verified mixed-span/coherent-word lemmas can combine
to recover the requested output up to the appropriate starred
structure equality. Printed reverse order equivalence is separate.
