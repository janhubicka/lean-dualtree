# Definition 26: the partial signature WORD DOMAIN fixes the last cut

The corrected forward signature contains the restriction of a
variable word to the STRICT forward-auxiliary initial segment
before its last interior cut t0. Although t0 is omitted from that
partial function, its DOMAIN encodes exactly the initial segment.

For any two distinct cuts u≠v in the same homogeneous ambient tree,
the corrected ForwardAux order compares u and v. The earlier of
u,v itself belongs to the strict initial segment of the later cut
but not to its own strict initial segment. Therefore the strict
domains cannot coincide.

The lemma is kernel checked in both raw and bounded homogeneous
tree types. In the bounded statement, u and v are actual indices,
so testing the smaller cut is legitimate and does not silently
extend the partial domain outside the word's universe.

This removes the need to assume a common last cut if equality of
the original Definition-26 signature is encoded faithfully as
equality of its partial word WITH ITS DOMAIN.

The printed paperAuxB uses reverse lex on equal-length positions;
this module proves only the forward repaired order. The eventual
literal fixed-signature theorem also needs equality of signature
trees and actual rooted symbols and then variable-word-level
Q surjectivity, not merely evaluation coverage.
