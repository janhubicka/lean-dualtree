# Lemma 27: unsafe late output roots are forced constants

An original ambient f-variable root u lies in the final interpolating
word f' only if it is retained at or before the inclusive cut or it
comes from a **selected** rank-budgeted local variable address.

If u is after the cut and its actual safeAddress is none, both
possibilities are impossible. Thus f' has the explicit fallback letter
at u. For an alphabet with at least two distinct letters, evaluated
span inclusion O.span ⊆ f'.span forces O's syntactic symbol at u to be
that SAME fallback constant.

Lean proofs in ForwardQFinalUnsafeOutputConstant:

* unsafe_late_root_not_final_support
* unsafe_late_interpolated_word_constant
* unsafe_late_output_word_constant

This proves the OUTPUT half of the last word-matching obligation.
The Q half is still open: selectedFrontier may exist at u even when
its inverse local tail is too long for the shortened local domain;
we must then prove sampledEnlarged returns fallback rather than
silently confusing no safe address with no selected frontier.

The full mixed-product Ramsey-span coherence, reconstruction of
target D2 marks, and starred-object equality remain separate.
