# Old source-variable visibility at true corrected cone projections

Let P_i(z) be a genuine projected original T node in the common safe
shortened cone of frontier_i.  Let v be an actual OLD source variable
whose root is a prefix of P_i(z).  Since both v and frontier_i prefix
P_i(z), they are comparable by prefix order.

The old source variable root is at or before the corrected inclusive
forward cut, while frontier_i is a minimal T node strictly OUTSIDE
the cut. If frontier_i were a prefix of v then v would also lie
outside, contradiction. Therefore v is a STRICT prefix of frontier_i.

The proof uses a generic list lemma: two prefixes of one finite
list are comparable by their lengths, proved explicitly via
List.take and List.take_append_drop. No ambient-immediate-child
hypothesis is needed.

The existing visible-ancestor list then includes v, and the
verified auxiliary Q decoder has a finite label in Fin(m+1)
which decodes to that exact dependent OLD variable. The selected
encoder's decode law is also registered for the actual P_i(z).

For a SAME-complete-signature starred refinement O, the prior
root-type equivalence will transport any old output variable
at a safe late original f-root back to its actual source
dependent variable. The O.word.below law then proves the
prefix premise automatically. That is the next small bridge
before defining the full local enlarged input words.

Still open: choosing D2 marked points to reconstruct O.tree,
proving the actual corrected W_* condition, exact Q(w)=O
starred-object equality, and the printed reverse-order theorem.
