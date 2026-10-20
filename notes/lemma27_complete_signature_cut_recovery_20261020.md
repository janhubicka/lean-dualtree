# 20 October: literal complete corrected signature, no common-cut assumption

The actual corrected Definition 26 signature is a PAIR:
  (signatureTree_at_maxInterior(O,cut),
   restricted rooted-symbol word on the STRICT forward initial domain).
The restricted word is represented as a function to Option, so its
domain is part of its mathematical value. Two partial words with
different domains are NOT identified by comparing values only where
both happen to be defined.

New general lemma: equality of those Option-valued partial words
forces equality of cuts, because the strict initial segment of
a linear order uniquely determines its upper endpoint. Both
cuts are proved to be genuine n-bounded nodes from the actual
StarredWord trees; no extra index-universe hypothesis is added.

The precise complete-signature comparison now recovers the common
cut, then uses the already certified
 Int(signatureTree(O,cut)) = Int(O.tree) \ {cut}
to recover the common interior and rooted partial symbols.
Consequently the existing algebraic early compatibility and
source-facing corrected Q coverage theorem applies to EVERY
evaluation of a starred refinement O inside the final f' span,
under equality of the complete corrected signature.

The result is an evaluated-word coverage statement, NOT equality
of starred VARIABLE-WORD objects with the Q output. Such object
equality would require the exact output tree skeleton and dependent
root-set/name correspondence, perhaps a stronger mixed Ramsey
construction with auxiliary coordinates. Printed reverse-order W_*
remains different and is not silently corrected by this result.
