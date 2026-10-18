# Total genuine ambient post-Ramsey substitution, 18 October 2026

The completed corrected final rank-budgeted T'_(m+q) is already
proved complete skew (for positive b,q). We have separately proved
exact ambient bounded-root typing, injection of selected local
variable tags, root-prefix preservation, and a unique partial
safe projected coordinate decoder.

This module constructs an ACTUAL total syntactic substitution
rho : ws(f) -> alphabet constant or selected T' root:
- safe projected ambient root u=P_i(z): use localSymbol(f_i,z);
- retained selected old root not in any safe cone: keep it;
- any other omitted/unsafe original root: send to fallback alpha.

For every selected global variable root v, rho(v) is exactly inr(v).
For every emitted variable rho(u)=inr(v), the selected root v
is an ambient prefix of the original f root u.

RootCompatibleRefinement.Certificate thus gives a LEGAL VariableWord
with EXACTLY T' as support and a syntactic/evaluated span subset
of the original ambient word f. At every safe projected original
f root, rho(P_i(z)) agrees exactly with decoded f_i.word(z).

Important remaining interface:
* compare this word's evaluation on ALL original ambient f fibres
  with the full corrected Q(s) of every mixed-span assignment;
* verify its stars/variable occurrences implement the specific
  selected local words with the correct expanded alphabet;
* transport Definition 24 simplicity and complete the Ramsey
  recursion/induction;
* reconcile corrected forward-order hypotheses with the printed
  reversed-starred W_* class.

No claim is made that merely having a legal word with correct
support and span inclusion is the full Lemma 27.
