# Literal forward Definition-26 signature-tree equality

The verified geometric identity in ForwardSignatureInteriorExact states:
  Int(signatureTree(O,t0)) = Int(O.tree) \ {t0}
for any actual corrected starred word O whose maximal interior
element is the given t0. This is the FIRST-BOUNDARY signature
tree, not a simplified interior-only proxy.

Fix one corrected source FibreFrame g and an actual starred output O
whose maximal interior cut is the SAME g.core.cut. If their
exact signatureTree_at_maxInterior objects agree and their
underlying bounded-root symbols agree on the STRICT forward initial
segment before t0, then:
- the geometric interior-minus-cut equivalence on both words gives
  Int(O.tree) = Int(g.core.source.tree), including t0 itself;
- the rooted symbol equality before the cut plus the atRoot
  axiom at the cut gives the previous ConcreteForwardSignature;
- the algebraic signature bridge proves every evaluated word of
  an O.word-span-refinement of f' has a genuine corrected starred
  Q evaluation witness in the post-Ramsey mixed-word span.

This derives the old interior compatibility from the LITERAL
signature tree instead of assuming it. The common-cut condition
is explicit: the paper's signature determines a canonical last
interior node, so one still needs to prove that a fixed signature
enforces the same cut when formalizing the full Definition-26 fibre.
More significantly, coverage here is of EVALUATED CONSTANT words,
whereas the original Q map acts on STARRED l-variable words and
monochromaticity concerns those objects.

Remaining: full typed fixed-signature membership, Q(w) = O as
variable-word-plus-tree (with correct auxiliary symbols),
Definition-24 simple-colour smooth pullback, and the repaired
forward-vs-printed reverse starred W_* interface.
