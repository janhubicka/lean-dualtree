# Lemma 27: exact raw Q preimage versus corrected D₂ admissibility

Status: **Lean CI passed and merged 22 October 2026** in
[#420](https://github.com/janhubicka/lean-dualtree/pull/420) and
[#421](https://github.com/janhubicka/lean-dualtree/pull/421).
The full Lemma 27, Lemma 28, Theorem 25, and the dual-tree Ramsey
theorem are **not** certified by these changes.

## Premises and exact raw reconstruction

Fix a corrected forward-ordered frame \`g\`, a local mixed Ramsey word
\`f\`, and a target starred word \`O\`. Assume:

- the *complete corrected* signatures of the source and \`O\` agree
  (including the domain of the strict partial rooted signature word);
- every vertex of \`O.tree\` belongs to the **actual rank-filtered**
  final support \`T'_{m+q}\`, not merely to the ambient complete \`T\`;
- the output word's evaluated span lies in the interpolated final
  word's evaluated span; and
- the alphabet has the two-letter property used in the exact
  evaluated-span/refinement conversion.

At every original literal source marker \`r\`, the target has **one
unique** corresponding terminal \`t_r\`. Its verified safe inverse
address gives a local D₂ variable root \`z_r\` of the **actual**
component \`f_i\`, indexed by the original sorted source frontier
\`i = bulletForMarker(r)\`.

These local roots form a genuine mixed-product span point. Relettering
the coordinate words coherently on each local *variable fibre*
supplies an enlarged-alphabet point \`w\` in the mapped mixed-word span
such that

\`\`\`
nodes(g.core, eraseAux(w)) = O.tree.toFinset
\`\`\`

and its complete fibrewise Q symbol function equals the dependent
word of \`O\` **at every ambient bounded position**, after the
verified old-root variable equivalence. The assertion does **not**
silently turn a finite *set* equality into equality of arbitrarily
enumerated tree lists.

This construction requires **no starred D₂ order assumption**,
but is a *raw* Q preimage. It cannot yet be used as an element of
the corrected starred input domain.

Formal Lean endpoint:
\`DualTree.ForwardQFinalTargetRankGap.exists_coherent_raw_target_Q_preimage\`.

## Exact remaining D₂ obstruction

For increasing selected D₂ indices \`i < j\`, denote:

- \`f_i\`: source minimal complete-T frontier at bullet index \`i\`;
- \`z_i\`: selected local marked tail above \`f_i\`;
- \`t_i = P_i(z_i)\`: the unique target terminal in that cone;
- \`F_i = h_T(f_i)\`, \`A_i = h_T(t_i)\`.

The genuine complete-support cone-height equation says

\`\`\`
A_i = F_i + |z_i|.
\`\`\`

The corrected starred domain requires \`|z_i| <= |z_j|\` for every
increasing selected D₂ pair. Equivalently,

\`\`\`
A_i + F_j <= A_j + F_i.     (1)
\`\`\`

The frontier ranks in the **actual corrected complete T** satisfy
\`F_i <= F_j\` and each belongs to the two-point set \`{m, m+1}\`,
where \`m = h_T(cut)\`. Therefore (1) is equivalent to the following
concrete, *target-only* conditions:

1. \`A_i <= A_j\` for every selected \`i < j\`;
2. \`A_i < A_j\` whenever additionally \`F_i < F_j\`.

There is **no** valid step replacing \`F_i\` and \`F_j\` by the same
rank: the two ranks can differ by one. In particular nondecreasing
target terminal ranks **alone** are insufficient if a source frontier
rank jump occurs; that pair needs a strict target rank jump.

The full chain of equivalences is registered and checked in:

- \`ForwardQFinalTargetRankGap.target_tail_length_le_iff_compensated_T_ranks\`;
- \`ForwardQFinalTargetRankGap.targetMixedPoint_starred_iff_target_rank_gaps\`;
- \`ForwardQFinalTargetRankBands.frontierTRank_mono\`;
- \`ForwardQFinalTargetRankBands.frontierTRank_band\`;
- \`ForwardQFinalTargetRankBands.target_rank_gaps_iff_terminal_rank_jump_order\`.

Under conditions (1) or the equivalent weak/strict rank criterion,
the raw preimage is promoted to a genuine corrected **starred**
mixed-product input in the enlarged local span, with the same
exact support and full word; see
\`ForwardQFinalTargetRankGap.exists_coherent_starred_target_Q_preimage_of_rank_gaps\`.

## Adversarial boundary and next proof task

**Not yet proved:** that *every* supported same-complete-signature
starred target \`O\` meeting the span hypotheses satisfies the above
terminal-rank monotonicity and strict jump condition.

The target is already semi-complete skew and inside \`T'_{m+q}\`,
but none of the checked theorems promotes those facts directly
to the required cross-frontier rank inequalities. The strict
condition when \`F_i=m\` and \`F_j=m+1\` should be attacked first.
It is also a precise finite counterexample search target: find a
supported equal-signature starred \`O\` with \`A_i = A_j\` across
a source frontier-rank jump, respecting **all** frame, support,
span, and rank-budget assumptions.

Relettering does not fix such an ordering violation: it leaves
the selected D₂ roots unchanged. One would have to modify the
input/root construction, restrict target refinements, or adjust
the Ramsey induction if the strict condition fails.

Separately, the original paper's reverse-lex \`W_*\` and the
corrected forward-lex \`W_*\` cannot be identified by naive
coordinate reindexing: the typed counterexample in
\`ForwardQStarredOrderReindexObstruction.lean\` remains valid.
The full starred Q object also needs a justified identification
of **tree-list representation** rather than merely finite node
sets. Finally, Lemmas 27–28 and the theorem still require the
remaining colouring-pullback, span-direction and numerical
induction bridges.

The proof-status distinctions here are intentional: **verified
raw reconstruction** is not **verified starred reverse coverage**.
