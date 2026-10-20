# Actual mixed-product alphabet lift and coherent span membership

The enlarged-alphabet step in Lemma 27 must not equate an arbitrary
mixed-product point with a point in the span of the post-Ramsey local
mixed variable word. The latter restricts coordinate words as well
as selected D1 and D2 marker points.

The Lean implementation now constructs a true alphabet lift of the
same local variable word, changing only constants while retaining
its actual dependent variable-root supports and all marker geometry.

Given a genuine base point in the original mixed-product span, ANY
assignment of an enlarged letter to every actual component variable
defines a new point in the span of this alphabet-lifted mixed word.
All occurrences of each given variable receive its one assigned
letter. This is the necessary algebraic span lemma, NOT a proof that
the desired output O produces a suitable assignment.

Remaining: derive variable-fibre constancy of the O-derived
`encodeProjectedOutputSymbol` from O.span ⊆ f'.span, and replace
pointwise witness choices by the value chosen at each component
variable ROOT. Then show Q still decodes to O at every P_i(z),
while maintaining the given D1/D2 marker choices. The full
starred-tree matching remains separate.
