# Lemma 27: closing new/new skew length clause III

The corrected forward-order final support is the union of retained
initial T roots and selected projected roots P_i(z). Source-facing
rank formulas give

  h_final(P_i(z)) = H_i + r_i(z),
  h_T(P_i(z))     = H_i + |z|,

where H_i belongs to {m,m+1}, while r_i(z) is the local support
intrinsic rank (NOT the raw local word length).

For selected projected roots with h_final(P_i(z)) <
h_final(P_j(w)), split the four combinations of H_i,H_j:

* H_i=H_j: r_i<r_j, so global vector-skew level separation
  gives |z|<|w|.
* H_i=m, H_j=m+1: r_i<=r_j. Strict local rank comparison
  gives |z|<|w|; equality gives |z|<=|w| using
  vector-skew same-level order and the proven i<j frontier order.
  The extra H_j unit forces strict ambient T rank growth.
* H_i=m+1, H_j=m: r_i+2<=r_j. The predecessor
  rank-gap lemma proves |z|+2<=|w|, overcoming the adverse
  frontier rank offset.
* H_i=H_j=m+1: handled like the first case.

Thus h_T(P_i(z))<h_T(P_j(w)), and the original complete T skew
clause III gives the required strict ambient word-length inequality.
This covers ALL selected new/new pairs, including equal or distinct
frontier indices, without assuming the final support is skew.

Remaining tasks: prove skew clause II at equal final intrinsic
ranks with ordinary lex ordering (cross-frontier projected
comparisons are delicate), establish the special skew witness IV,
then glue f' with its full span inclusion and complete the Ramsey
iteration. The published reverse-starred domain and canonical I_U
alignment are still open.
