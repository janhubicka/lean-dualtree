# Lemma 27: two-band frontier arithmetic (17 October 2026)

This note targets only the remaining projected/projected
skew length conditions of the **corrected forward-order** construction.

Write H_i = height_T(frontier_i), and r_i(z) for the intrinsic
height of z in the local coordinate support. The kernel-checked
rank identities say

  height_(T'_M)(P_i z) = H_i + r_i(z),
  height_T(P_i z)     = H_i + |z|,

with H_i in {m,m+1}. The two height functions are DIFFERENT.
Length comparison in the original skew ambient T follows from
an inequality of the second expressions, not automatically
from an inequality of the first.

New theorem interface (`ForwardQFinalFrontierRankOrder`):
whenever H_i < H_j, the sorted coordinate indices satisfy i < j.
Thus rank-m frontiers precede all rank-(m+1) frontiers under the
actual length-first ForwardAux enumeration. This is NOT the
claim that their ordinary lex order coincides.

For projected/projected final clause (iii), let H_i+r < H_j+s.
Three cases must be distinguished:

1. H_i=H_j: r<s. Vector complete support strictly separates
   different local intrinsic levels across coordinates, giving
   |z|<|w| and hence H_i+|z|<H_j+|w|.
2. H_i=m, H_j=m+1: necessarily r<=s and i<j.
   For r=s, vector same-level order gives |z|<=|w|;
   for r<s, global level separation gives |z|<|w|.
   Either way the extra frontier unit gives strict ambient rank.
3. H_i=m+1, H_j=m: necessarily r+2<=s. One needs the
   QUANTITATIVE strengthening |z|+2<=|w|, not just |z|<|w|.
   This should follow by choosing a support node at intermediate
   intrinsic local rank r+1 and applying successive-level
   separation TWICE, provided the requisite level nonemptiness
   is extracted from q-completeness. This is an *unproved
   proof obligation* until all quantifiers are checked in Lean.

For final clause (ii), H_i+r=H_j+s. If the frontier ranks
differ, the local ranks differ by exactly one. One must also
control ordinary lex orientation of the two incomparable
frontier cones; sorting by ForwardAux alone does NOT suffice.
No complete final skewB claim follows from the two-band
rank arithmetic alone.

For skew witness (iv), neither a rank/length argument nor
the q=1 upper-band emptiness can be waved away. Exact
branching and the unique final witness remain separate.

Do not silently replace source Definition 24 simplicity by
the checked source-relative selector, and do not use a
reversed W_* order as if it were the corrected forward Q.

## Checked forward-band equal-local-rank case (new endpoint)

For H_i=m and H_j=m+1 with equal local ranks,
the rank-order theorem gives i<j. The vector-skew same-level
constraint gives |z| <= |w|; hence the ambient T intrinsic
ranks satisfy m+|z| < (m+1)+|w|, and original complete-T
skew clause (iii) yields |P_i(z)|<|P_j(w)|.
This is precisely the same-local-rank subcase of strict
projected/projected final skew clause (iii). The new proof
does not require T'_M to be globally skew, and does not
assert any remaining rank-gap or ordinary-lex orientations.
