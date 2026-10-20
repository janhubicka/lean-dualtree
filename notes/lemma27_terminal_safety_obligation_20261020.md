# Necessary terminal-safety obligation for exact Lemma 27 Q surjectivity

Every actual corrected Q terminal is the projection of a literal
D2 marked point of the local mixed product. The proofs establish
that it has an actual safeAddress of the form
`some (i, x.bulletPoint i)`, where the tail lies inside the
shortened local height `k-(m+1)`.

Conversely, a vertex of an actual Q tree with safeAddress=none
must belong to its old interior and cannot be a terminal.

Consequently, exact Q-tree equality with an arbitrary requested
starred output O requires EVERY terminal of O.tree to lie in
the safe shortened projection image. This is a NEW EXPLICIT
necessary geometric condition independent of the full word
equality already formalized in PRs #403-#407.

Adversarial warning: the source's same-complete-signature and
O.word.span⊆f'.span hypotheses constrain the interior, variables
and word symbols, but do not immediately bound the inverse tails
of terminal points of O.tree. Before asserting complete Lemma 27
surjectivity, prove that the relevant target class implies safe
terminal addresses, or restrict the target class appropriately.

Even safe terminals alone do not guarantee admissible D1/D2
marked points in the mixed Ramsey span or the corrected starred
ordering requirement. Those remain genuine proof obligations.
