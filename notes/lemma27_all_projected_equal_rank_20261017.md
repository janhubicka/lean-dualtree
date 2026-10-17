# Projected/projected equal-final-rank skew-II case split

The full selected new/new clause II reduces to three disjoint cases.
The exact final height formula (H_i+ri) is NOT interchangeable with
ambient original-T height (H_i+|z_i|).

(1) Identical frontier index: equal final ranks give equal local support
ranks; the complete-T projection preserves/reflects ordinary lex,
so the local skew-II inequality |z|<=|w| transfers via ambient T skew-II/III.

(2) Distinct indices, same frontier T rank: lex order of projected cones
forces i<j by their certified incomparability and the lex antisymmetry
of finite words. Equal final ranks give ri=rj. The vector-complete
same-level ordering yields |z|<=|w|. Thus ambient T rank is weakly
increasing, so actual projected lengths are weakly increasing.

(3) Distinct frontier ranks: the rank-(m+1) cone is ordinary-lex to
the LEFT of the rank-m cone, even though the latter appears earlier
in sorted forward auxiliary order. Therefore only
H_i=m+1, H_j=m is compatible with the lemma's given lex direction.
Equality of final ranks gives rj=ri+1; the vector-complete
successive-level inequality gives |z|<|w|.
This offsets the one-unit frontier-rank decrease, giving weak
original T rank increase and hence weak ambient length increase.

For the reverse ordinary-lex orientation, antisymmetry and the actual
injective projection yield a contradiction across distinct frontier indices.

These arguments rely exclusively on the repaired forward Frame,
not the printed reverse-starred W_* hypothesis.
The special skew witness IV and assembly of f' remain open.
