# Concrete strict-prefix signature bridge (forward-order repair)

The fixed signature in Definition 26 consists of a signature tree S'
and a partial word g' on the STRICT auxiliary initial segment D
before the last source interior t0. A source-facing technical point:
the strict D excludes the cut t0 itself, although t0 is a variable
root shared by every starred object with this source interior.

For the corrected forward order, equality of source and target
starred interiors gives equality of their variable-root supports
as SETS, without requiring identical list enumeration. Hence
every old source root is also a genuine target root.
Equality of rooted underlying symbols at each bounded position
strictly before cut is the signature's partial-word condition.
At the cut, the two VariableWord.atRoot axioms yield the same
underlying variable name (the cut's original bounded position).

Thus these two CONCRETE signature components imply the earlier
FixedEarlySignature certificate, and every constant evaluation
of a starred output O with these components and
span(O.word)⊆span(f') is realized by an actual corrected starred
mixed-product Q evaluation.

This avoids both mistakes:
- treating [S,f'] as the full set of independent f' evaluations;
- silently assuming that the signature's strict prefix-word
  condition includes t0.

The remaining significant proof step is to tie the literal
ForwardStarredSignature.signatureTree equality on arbitrary
starred refinements to sameInterior (via existing interior-
exactness results and the fact that their cuts coincide),
and to show Q hits the STARRED VARIABLE WORD itself, not only
its set of constant evaluations. Those steps, Definition 24
simple-colouring transport, and the printed reverse-order
counterexample are still open.
