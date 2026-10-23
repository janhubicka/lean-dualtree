# Lemma 27: intermediate raw Q preimage and D₂ rank-gap diagnosis

> **Resolved on 23 October 2026.** This file records the *intermediate*
> rank-gap diagnosis from 22 October. The outstanding corrected D₂
> starred-input order was subsequently proved from the actual target's
> skew clauses II/III and the two frontier rank bands, in merged
> PRs #423–425. PR #426 packaged the resulting full fibrewise Q
> preimage as a genuine typed starred word. See
> [the verified 23 October account](lemma27_target_D2_starred_from_skew_20261023.md).
> Printed reverse-lex W_* versus corrected forward W_* and the final
> Ramsey induction remain open.


Status: **Lean CI passed and merged 22 October 2026** in
[#420](https://github.com/janhubicka/lean-dualtree/pull/420) and
[#421](https://github.com/janhubicka/lean-dualtree/pull/421).
The full Lemma 27, Lemma 28, Theorem 25, and the dual-tree Ramsey
theorem are **not** certified by these changes.

## Premises and exact raw reconstruction

Fix a corrected forward-ordered frame `g`, a local mixed Ramsey word
`f`, and a target starred word `O`. Assume:

- the *complete corrected* signatures of the source and `O` agree
  (including the domain of the strict partial rooted signature word);
- every vertex of `O.tree` belongs to the **actual rank-filtered**
  final support `T'_{m+q}`, not merely to the ambient complete `T`;
- the output word's evaluated span lies in the interpolated final
  word's evaluated span; and
- the alphabet has the two-letter property used in the exact
  evaluated-span/refinement conversion.

At every original literal source marker `r`, the target has **one
unique** corresponding terminal `t_r`. Its verified safe inverse
address gives a local D₂ variable root `z_r` of the **actual**
component `f_i`, indexed by the original sorted source frontier
`i = bulletForMarker(r)`.

These local roots form a genuine mixed-product span point. Relettering
the coordinate words coherently on each local *variable fibre*
supplies an enlarged-alphabet point `w` in the mapped mixed-word span
such that

```
nodes(g.core, eraseAux(w)) = O.tree.toFinset
```

and its complete fibrewise Q symbol function equals the dependent
word of `O` **at every ambient bounded position**, after the
verified old-root variable equivalence. The assertion does **not**
silently turn a finite *set* equality into equality of arbitrarily
enumerated tree lists.

At the time of this 22 October proof, the witness was a **raw**
Q preimage without a verified starred-input certificate. The
additional certificate and actual typed starred output were
subsequently proved in PRs #425–426.

Formal Lean endpoint:
`DualTree.ForwardQFinalTargetRankGap.exists_coherent_raw_target_Q_preimage`.

## Exact remaining D₂ obstruction

For increasing selected D₂ indices `i < j`, denote:

- `f_i`: source minimal complete-T frontier at bullet index `i`;
- `z_i`: selected local marked tail above `f_i`;
- `t_i = P_i(z_i)`: the unique target terminal in that cone;
- `F_i = h_T(f_i)`, `A_i = h_T(t_i)`.

The genuine complete-support cone-height equation says

```
A_i = F_i + |z_i|.
```

The corrected starred domain requires `|z_i| <= |z_j|` for every
increasing selected D₂ pair. Equivalently,

```
A_i + F_j <= A_j + F_i.     (1)
```

The frontier ranks in the **actual corrected complete T** satisfy
`F_i <= F_j` and each belongs to the two-point set `{m, m+1}`,
where `m = h_T(cut)`. Therefore (1) is equivalent to the following
concrete, *target-only* conditions:

1. `A_i <= A_j` for every selected `i < j`;
2. `A_i < A_j` whenever additionally `F_i < F_j`.

There is **no** valid step replacing `F_i` and `F_j` by the same
rank: the two ranks can differ by one. In particular nondecreasing
target terminal ranks **alone** are insufficient if a source frontier
rank jump occurs; that pair needs a strict target rank jump.

The full chain of equivalences is registered and checked in:

- `ForwardQFinalTargetRankGap.target_tail_length_le_iff_compensated_T_ranks`;
- `ForwardQFinalTargetRankGap.targetMixedPoint_starred_iff_target_rank_gaps`;
- `ForwardQFinalTargetRankBands.frontierTRank_mono`;
- `ForwardQFinalTargetRankBands.frontierTRank_band`;
- `ForwardQFinalTargetRankBands.target_rank_gaps_iff_terminal_rank_jump_order`.

Under conditions (1) or the equivalent weak/strict rank criterion,
the raw preimage is promoted to a genuine corrected **starred**
mixed-product input in the enlarged local span, with the same
exact support and full word; see
`ForwardQFinalTargetRankGap.exists_coherent_starred_target_Q_preimage_of_rank_gaps`.

## Resolution and remaining work (23 October 2026)

The specific question raised by this note has been **settled in Lean**.
The target's intrinsic terminal levels agree with the selected
source-frontier T-rank bands. In equal bands, O's skew II and T's
skew III imply nondecreasing terminal T-ranks. Across a frontier
rank jump, O's skew III forces strictly increasing terminal lengths,
while the high-band cone lies earlier in ordinary lex; T's skew
II/III then exclude both equal and decreasing T-ranks. Therefore
the corrected D₂ point tuple satisfies its vector-one-complete
starred condition without any new hypothesis.

See [the full verified proof and source anchors](lemma27_target_D2_starred_from_skew_20261023.md).
The 22 October observation remains useful as the exact numerical
criterion, but it is **no longer an open lemma**.

The original printed reverse-lex mixed-product starred domain still
does not automatically translate to the forward-corrected domain.
Unrestricted final-span reverse coverage still has the extra-retained
root obstruction, and the printed Definition 24 selector and Ramsey
iteration remain to be reconciled. Equality of arbitrary list
enumerations is not claimed; the typed Q output agrees with the
target's finite node **set** and entire rooted dependent word.
