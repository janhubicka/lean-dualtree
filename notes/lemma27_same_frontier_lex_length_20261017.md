# Adversarial case separation for final skew II (17 October 2026)

This proof branch proves only the *same-frontier* projected equal-final-rank
case and a reusable complete-ambient-T length transfer lemma.
At a fixed frontier, the true projection is an inverse-address concatenation
followed by a certified complete-tree canonical embedding. That embedding
preserves ordinary lex, and its injectivity plus totality gives reflection.
Do not assume that the length-first sorted frontier order IS ordinary lex.

For same-final-rank roots at one fixed frontier, local intrinsic ranks
agree. Local complete-skew clause II gives |z| <= |w| in the direction
of local (equivalently projected) lex. The ambient complete T rank formulas
then imply h_T(P_i z) <= h_T(P_i w), and original T skew II/III imply
|P_i z| <= |P_i w|.

Remaining projected equal-final-rank cases:
(1) distinct same-band frontiers; the true lex order dictates index order
and vector-complete same-level inequality,
(2) lower rank m frontier versus upper m+1 frontier, whose ordinary lex
orientation is forbidden by the newly verified cross-band lemma,
(3) upper m+1 frontier versus lower rank m frontier, whose local ranks
differ by one; successive-level separation gives a one-unit tail gap.

Retained/retained and old/new equal-rank cases are already checked.
The witness clause IV and original paper's starred-domain equivalence remain open.
