# Lemma 27: verified corrected starred target Q preimage

**Status (23 October 2026):** The relevant Lean source declarations passed
the complete DualTree umbrella build, finite regressions, and transitive
axiom audit. The work was merged in
[#423](https://github.com/janhubicka/lean-dualtree/pull/423),
[#424](https://github.com/janhubicka/lean-dualtree/pull/424),
[#425](https://github.com/janhubicka/lean-dualtree/pull/425), and
[#426](https://github.com/janhubicka/lean-dualtree/pull/426).
This is a theorem in the **globally forward-corrected** construction.
It does **not** by itself validate the printed reverse-lex formulation
of Lemma 27, the subsequent Ramsey iteration, or Theorem 3.

## Precise target assumptions

Fix the actual corrected forward source frame g, a genuine local mixed
Ramsey variable word f, and the target starred word O. Assume that

1. O has the same **complete corrected signature** as the source,
   including the strict partial-word domain, so its maximal interior
   cut and original interior roots are identified rigorously;
2. every target tree node lies inside the **rank-filtered final support**
   T'_(m+q), not merely inside the ambient complete support T;
3. O.word.span is contained in the evaluated span of the interpolated
   final word, and the alphabet has the stated two-letter property;
4. a choice of values on the final variable roots is supplied (the
   existence theorem is valid for each such choice).

All starred and complete-skew predicates here use the corrected
length-first **forward** lexicographic auxiliary order. The target O
already carries its true semi-complete-skew proof in its type.

The target terminal at each selected D₂ source-frontier index is
chosen by the verified original-literal-marker/target-leaf
correspondence and safe inverse cone address. It is a genuine local
variable support point of the actual component word f_i. Coherent
relettering makes the coordinate words constant on each local
variable fibre, so the resulting enlarged point is in the real
alphabet-lifted mixed-product span.

## Previously outstanding D₂ condition is now proved

For sorted selected indices i < j, put

- f_i = the actual source minimal outside-cut frontier of T;
- z_i = the actual target-selected local D₂ point at frontier i;
- t_i = P_i(z_i), the unique corresponding target O terminal;
- F_i = h_T(f_i), A_i = h_T(t_i), and m = h_T(cut).

The original complete-support cone equation gives

    A_i = F_i + |z_i|.

The corrected starred D₂ predicate is exactly the vector-one
condition that |z_i| <= |z_j| for all selected i < j. Equivalently,

    A_i + F_j <= A_j + F_i.

The actual source T-frontier ranks are nondecreasing and in {m,m+1}.
Thus the required inequality holds exactly when A_i <= A_j for
ordered indices, with a **strict** A_i < A_j whenever F_i < F_j.

The four newly checked steps settle this without assuming D₂ order:

**1. Target-intrinsic rank identification (PR #423).** Equality of
the target's tree node **Finset** with the reconstructed Q support
implies equality of every intrinsic predecessor count. The source
Q/frontier band correspondence transfers to the genuine target O:

    h_O(t_i) = h_O(cut)       if F_i = m;
    h_O(t_i) = h_O(cut) + 1   if F_i = m+1.

No equality of arbitrary tree-list enumerations is used.

**2. Real target skew-length inequalities (PR #424).** At equal
frontier ranks, the actual projected cones occur in forward ordinary
lex order as the selected indices increase. Their target-intrinsic
ranks are equal, so **O's own skew clause (ii)** yields
|t_i| <= |t_j|.

At a jump F_i=m to F_j=m+1, the target-intrinsic ranks strictly
increase. Hence **O's skew clause (iii)** gives |t_i| < |t_j|.
Crucially, the higher-frontier-rank cone is *ordinary-lex earlier*
than the lower-frontier-rank cone.

**3. Target ambient T-rank ordering (PR #425).** In a common
frontier band, a hypothetical A_j < A_i would contradict the
target length inequality by complete T's skew clause (iii).
Thus A_i <= A_j.

At a frontier-rank jump, A_j < A_i contradicts target's strictly
increasing terminal lengths by complete T's skew clause (iii).
If A_j = A_i, the reversed ordinary lex ordering and complete
T's skew clause (ii) force |t_j| <= |t_i|, again contradicting
|t_i| < |t_j|. Therefore A_i < A_j.

By the compensated-rank equivalence, the **exact selected mixed
point automatically satisfies the corrected D₂ vector-one-complete
starred input predicate**. This removes the old standalone
BulletLengthsOrdered hypothesis.

**4. Actual typed Q output (PR #426).** Coherent relettering preserves
the genuine starred D₂ points. The final witness is an element of
ForwardQEnlargedConstantWords.EnlargedStarredInput, belonging to the
alphabet-lifted local mixed-word span. Applying the existing full
fibrewise Q construction yields an **actual**
StarredSignature.StarredWord. Its finite node set equals
O.tree.toFinset and every symbol of its dependent variable word
equals O's symbol under the verified source/target variable-root
equivalence, at every bounded ambient position.

## Kernel-checked interfaces

- DualTree.ForwardQFinalTargetIntrinsicBands.target_heightAt_eq_actual_Q
- DualTree.ForwardQFinalTargetIntrinsicBands.target_terminal_O_T_frontier_rank_band
- DualTree.ForwardQFinalTargetSkewLengths.target_terminal_length_le_same_frontier_rank
- DualTree.ForwardQFinalTargetSkewLengths.target_terminal_length_lt_frontier_jump
- DualTree.ForwardQFinalTargetOrderFromSkew.target_T_rank_mono_same_frontier_band
- DualTree.ForwardQFinalTargetOrderFromSkew.target_T_rank_strict_frontier_jump
- DualTree.ForwardQFinalTargetOrderFromSkew.targetMixedPoint_isStarred
- DualTree.ForwardQFinalTargetOrderFromSkew.exists_coherent_starred_target_Q_preimage
- DualTree.ForwardQFinalTypedTargetPreimage.exists_typed_corrected_Q_starred_target_preimage

The full target Q theorem is conditional only on the explicitly
stated legitimate signature, support, two-letter, span, and frame
requirements—not a separate D₂ order or target-terminal-rank
inequality.

## Remaining mathematical and manuscript obligations

- **Printed versus corrected domain.** The paper orders equal-length
  frontiers by *reverse* lex, while the coherent repaired geometry
  uses *forward* lex. The typed example in
  ForwardQStarredOrderReindexObstruction proves that naive
  reindexing can destroy the original W_* starred constraint.
  A paper correction or a new transport/Ramsey construction is needed.
- **Reverse span and retained roots.** The verified exact *target*
  preimage is a local theorem under target membership in the final
  support and the target evaluated-span premise. It does not assert
  unrestricted reverse coverage of the entire constructed final
  f' span. ForwardQFinalReverseCoverageCriterion proves an actual
  retained-root obstruction for that stronger statement.
- **Theorem 25 colouring induction.** A corrected intrinsic-root
  canonical selector already has smooth pullback and a total smooth
  extension in ForwardSemiCompleteCanonicalRoot. Matching the
  *published* Definition 24 selector, the required Ramsey iteration,
  and the recursive numerical parameter bounds remain separate.
- **Representation.** Finite support *sets* and whole dependent
  rooted words have been identified. No claim of equality of
  arbitrary list enumerations is made or required for the
  isomorphism-invariant statement.

In particular the 22 October target-rank-gap note was an accurate
intermediate diagnosis; its final *open ordering* paragraph is
superseded by this verified result.
